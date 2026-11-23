/*
 * main.m — AppKit spike for safe-pdf (task 11.1, Plan.md §6 Phase 11).
 *
 * A minimal native shell over the C API of safepdf_core.h: one window, an NSScrollView
 * whose document view stacks every page vertically (continuous scrolling with AppKit's own
 * momentum and elasticity), zoom through NSScrollView magnification (pinch, Cmd+ / Cmd- /
 * Cmd-0), pages rendered by the verified core on one background thread at
 * magnification x backingScaleFactor pixels per point (sharp on Retina), File > Open... via
 * NSOpenPanel or a path argument.
 *
 * Unverified shell code (Plan.md §8): it only displays pixels the core produced.
 *
 * Self-test (no window, never activates): SAFEPDF_MACOS_SELFTEST=DIR macos/build/safepdf-mac FILE
 * sets the activation policy to Prohibited before anything else, renders through the C API
 * and through the real view hierarchy (off screen, into NSBitmapImageReps), writes PNGs and
 * timings.txt into DIR, and exits.
 */
#import <AppKit/AppKit.h>
#include <mach/mach_time.h>
#include "safepdf_core.h"

static const CGFloat kGap = 12;     /* points between pages and around them */
static const CGFloat kMinMag = 0.1, kMaxMag = 8.0, kStep = 1.25;

static double nowMs(void) {
    static mach_timebase_info_data_t tb;
    if (tb.denom == 0) mach_timebase_info(&tb);
    return (double)mach_absolute_time() * tb.numer / tb.denom / 1e6;
}

static double gProcessStartMs;

/* ---------- render thread ---------- */

/* A finished render, handed from the render thread to the main thread. */
@interface RenderResult : NSObject
@property NSInteger page;
@property NSInteger scaleKey;   /* zoom in thousandths of a pixel per point */
@property (strong) id image;    /* CGImageRef bridged, or nil */
@property double ms;
@property (copy) NSString *error;
@end
@implementation RenderResult
@end

/* One dedicated NSThread registered with the Lean runtime; jobs arrive by
   performSelector:onThread:. */
@interface Renderer : NSObject
@property (strong) NSThread *thread;
@property (atomic) NSInteger generation;
- (void)renderDoc:(safepdf_doc *)doc page:(NSInteger)page scaleKey:(NSInteger)key
       generation:(NSInteger)gen done:(void (^)(RenderResult *))done;
@end

static void releaseBuffer(void *info, const void *data, size_t size) {
    (void)info; (void)size;
    free((void *)data);
}

static CGImageRef imageFromRender(safepdf_image *img) {
    CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
    CGDataProviderRef dp = CGDataProviderCreateWithData(NULL, img->rgba, img->stride * img->height,
                                                        releaseBuffer);
    CGImageRef ci = CGImageCreate(img->width, img->height, 8, 32, img->stride, cs,
                                  kCGImageAlphaNoneSkipLast | kCGBitmapByteOrderDefault, dp, NULL,
                                  false, kCGRenderingIntentDefault);
    CGDataProviderRelease(dp);
    CGColorSpaceRelease(cs);
    img->rgba = NULL; /* now owned by the data provider */
    return ci;
}

@implementation Renderer
- (instancetype)init {
    if ((self = [super init])) {
        _thread = [[NSThread alloc] initWithTarget:self selector:@selector(threadMain) object:nil];
        _thread.name = @"safepdf-render";
        _thread.qualityOfService = NSQualityOfServiceUserInitiated;
        [_thread start];
    }
    return self;
}
- (void)threadMain {
    safepdf_thread_enter();
    [NSTimer scheduledTimerWithTimeInterval:1e9 repeats:YES block:^(NSTimer *t) { (void)t; }];
    while (true) @autoreleasepool {
        [[NSRunLoop currentRunLoop] runMode:NSDefaultRunLoopMode beforeDate:[NSDate distantFuture]];
    }
}
- (void)runJob:(void (^)(void))job { job(); }
- (void)renderDoc:(safepdf_doc *)doc page:(NSInteger)page scaleKey:(NSInteger)key
       generation:(NSInteger)gen done:(void (^)(RenderResult *))done {
    void (^job)(void) = ^{
        RenderResult *res = [RenderResult new];
        res.page = page;
        res.scaleKey = key;
        if (gen != self.generation) { res.error = @"stale"; }
        else {
            safepdf_image img;
            char *err = NULL;
            double t0 = nowMs();
            if (safepdf_render(doc, (size_t)page, (uint32_t)key, 1000, &img, &err) == 0) {
                CGImageRef ci = imageFromRender(&img);
                res.image = (__bridge_transfer id)ci;
            } else {
                res.error = [NSString stringWithUTF8String:err ? err : "render failed"];
                free(err);
            }
            res.ms = nowMs() - t0;
        }
        dispatch_async(dispatch_get_main_queue(), ^{ done(res); });
    };
    [self performSelector:@selector(runJob:) onThread:self.thread withObject:[job copy]
            waitUntilDone:NO];
}
@end

/* ---------- the page view ---------- */

@interface PageView : NSView
@property (nonatomic) safepdf_doc *doc;
@property (strong) Renderer *renderer;
@property (strong) NSMutableDictionary<NSNumber *, RenderResult *> *cache; /* page -> best image */
@property (strong) NSMutableSet<NSString *> *inflight;                     /* "page@key" */
@property (nonatomic) CGFloat scaleOverride;  /* > 0: pixels per point instead of window's */
@property (nonatomic) CGFloat magnification;  /* the scroll view's, kept in sync */
@property (copy) void (^onRender)(RenderResult *);
- (NSRect)pageRect:(NSInteger)i;
- (NSInteger)pendingCount;
@end

@implementation PageView {
    NSMutableArray<NSValue *> *_rects;
    CGFloat _width, _height;
}
- (BOOL)isFlipped { return YES; }
- (BOOL)isOpaque { return YES; }

- (void)setDoc:(safepdf_doc *)doc {
    _doc = doc;
    self.cache = [NSMutableDictionary dictionary];
    self.inflight = [NSMutableSet set];
    self.renderer.generation += 1;
    _rects = [NSMutableArray array];
    CGFloat maxW = 0, y = kGap;
    size_t n = doc ? safepdf_page_count(doc) : 0;
    for (size_t i = 0; i < n; i++) {
        double w = 612, h = 792;
        safepdf_page_size(doc, i, &w, &h);
        [_rects addObject:[NSValue valueWithRect:NSMakeRect(0, y, w, h)]];
        y += h + kGap;
        maxW = MAX(maxW, w);
    }
    _width = maxW + 2 * kGap;
    _height = MAX(y, 2 * kGap);
    for (NSUInteger i = 0; i < _rects.count; i++) { /* centre each page */
        NSRect r = _rects[i].rectValue;
        r.origin.x = floor((_width - r.size.width) / 2);
        _rects[i] = [NSValue valueWithRect:r];
    }
    [self setFrameSize:NSMakeSize(_width, _height)];
    [self setNeedsDisplay:YES];
}

- (NSRect)pageRect:(NSInteger)i { return _rects[i].rectValue; }

- (CGFloat)pixelsPerPoint {
    CGFloat backing = self.scaleOverride > 0 ? self.scaleOverride
                    : (self.window ? self.window.backingScaleFactor : 1);
    return backing * (self.magnification > 0 ? self.magnification : 1);
}

- (NSInteger)wantedKey { return (NSInteger)llround([self pixelsPerPoint] * 1000); }

- (NSInteger)pendingCount { return (NSInteger)self.inflight.count; }

- (void)requestPage:(NSInteger)i key:(NSInteger)key {
    RenderResult *have = self.cache[@(i)];
    if (have && have.scaleKey == key) return;
    NSString *tag = [NSString stringWithFormat:@"%ld@%ld", (long)i, (long)key];
    if ([self.inflight containsObject:tag]) return;
    [self.inflight addObject:tag];
    __weak PageView *weakSelf = self;
    NSInteger gen = self.renderer.generation;
    [self.renderer renderDoc:self.doc page:i scaleKey:key generation:gen done:^(RenderResult *res) {
        PageView *me = weakSelf;
        if (!me) return;
        [me.inflight removeObject:tag];
        if (gen != me.renderer.generation) return;
        if (res.image) {
            RenderResult *old = me.cache[@(i)];
            /* keep the image closest to the current scale */
            NSInteger want = [me wantedKey];
            if (!old || labs(res.scaleKey - want) <= labs(old.scaleKey - want)) me.cache[@(i)] = res;
            [me setNeedsDisplayInRect:[me pageRect:i]];
        } else if (res.error && ![res.error isEqualToString:@"stale"]) {
            NSLog(@"page %ld: %@", (long)i + 1, res.error);
        }
        if (me.onRender) me.onRender(res);
    }];
}

/* Request renders for the pages intersecting `visible` (plus one on each side) at the
   current scale; drop cached images of pages far away. */
- (void)updateForVisibleRect:(NSRect)visible {
    if (!self.doc) return;
    NSInteger key = [self wantedKey];
    NSInteger first = -1, last = -1;
    for (NSUInteger i = 0; i < _rects.count; i++) {
        if (NSIntersectsRect(_rects[i].rectValue, visible)) {
            if (first < 0) first = (NSInteger)i;
            last = (NSInteger)i;
        }
    }
    if (first < 0) return;
    for (NSInteger i = first; i <= last; i++) [self requestPage:i key:key];
    if (first > 0) [self requestPage:first - 1 key:key];
    if (last + 1 < (NSInteger)_rects.count) [self requestPage:last + 1 key:key];
    for (NSNumber *k in self.cache.allKeys) {
        if (k.integerValue < first - 3 || k.integerValue > last + 3) [self.cache removeObjectForKey:k];
    }
}

- (void)drawRect:(NSRect)dirty {
    [[NSColor colorWithWhite:0.45 alpha:1] setFill];
    NSRectFill(dirty);
    CGContextRef cg = [[NSGraphicsContext currentContext] CGContext];
    CGContextSetInterpolationQuality(cg, kCGInterpolationHigh);
    for (NSUInteger i = 0; i < _rects.count; i++) {
        NSRect r = _rects[i].rectValue;
        if (!NSIntersectsRect(r, dirty)) continue;
        [[NSColor whiteColor] setFill];
        NSRectFill(r);
        RenderResult *res = self.cache[@(i)];
        if (res.image) {
            CGImageRef ci = (__bridge CGImageRef)res.image;
            /* flipped view: draw the top-down image right side up */
            CGContextSaveGState(cg);
            CGContextTranslateCTM(cg, r.origin.x, r.origin.y + r.size.height);
            CGContextScaleCTM(cg, 1, -1);
            CGContextDrawImage(cg, CGRectMake(0, 0, r.size.width, r.size.height), ci);
            CGContextRestoreGState(cg);
        }
    }
    [self updateForVisibleRect:self.visibleRect];
}
@end

/* Centres the document view when it is narrower than the clip view. */
@interface CenteringClipView : NSClipView
@end
@implementation CenteringClipView
- (NSRect)constrainBoundsRect:(NSRect)proposed {
    NSRect r = [super constrainBoundsRect:proposed];
    NSView *doc = self.documentView;
    if (doc && r.size.width > doc.frame.size.width)
        r.origin.x = -floor((r.size.width - doc.frame.size.width) / 2);
    return r;
}
@end

/* ---------- controller ---------- */

@interface Controller : NSObject <NSApplicationDelegate, NSWindowDelegate>
@property (strong) NSWindow *window;
@property (strong) NSScrollView *scroll;
@property (strong) PageView *pages;
@property (nonatomic) safepdf_doc *doc;
@property (copy) NSString *initialPath;
- (void)buildViewsWithFrame:(NSRect)frame;
- (BOOL)openPath:(NSString *)path;
@end

@implementation Controller
- (void)buildViewsWithFrame:(NSRect)frame {
    self.scroll = [[NSScrollView alloc] initWithFrame:frame];
    self.scroll.contentView = [[CenteringClipView alloc] initWithFrame:frame];
    self.scroll.hasVerticalScroller = YES;
    self.scroll.hasHorizontalScroller = YES;
    self.scroll.autohidesScrollers = YES;
    self.scroll.allowsMagnification = YES;
    self.scroll.minMagnification = kMinMag;
    self.scroll.maxMagnification = kMaxMag;
    self.scroll.backgroundColor = [NSColor colorWithWhite:0.45 alpha:1];
    self.scroll.autoresizingMask = NSViewWidthSizable | NSViewHeightSizable;
    self.pages = [[PageView alloc] initWithFrame:NSMakeRect(0, 0, 100, 100)];
    self.pages.renderer = [Renderer new];
    self.pages.magnification = 1;
    self.scroll.documentView = self.pages;
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(magnifyEnded:)
        name:NSScrollViewDidEndLiveMagnifyNotification object:self.scroll];
}

- (void)magnifyEnded:(NSNotification *)n {
    (void)n;
    [self syncMagnification];
}

- (void)syncMagnification {
    self.pages.magnification = self.scroll.magnification;
    [self.pages setNeedsDisplay:YES];
}

- (BOOL)openPath:(NSString *)path {
    char *err = NULL;
    double t0 = nowMs();
    safepdf_doc *d = safepdf_open(path.fileSystemRepresentation, &err);
    if (!d) {
        NSString *msg = [NSString stringWithUTF8String:err ? err : "cannot open"];
        free(err);
        if (self.window) {
            NSAlert *a = [NSAlert new];
            a.messageText = [NSString stringWithFormat:@"Cannot open %@", path.lastPathComponent];
            a.informativeText = msg;
            [a runModal];
        } else {
            fprintf(stderr, "cannot open %s: %s\n", path.UTF8String, msg.UTF8String);
        }
        return NO;
    }
    NSLog(@"opened %@ (%zu pages) in %.1f ms", path.lastPathComponent, safepdf_page_count(d),
          nowMs() - t0);
    safepdf_doc *old = self.doc;
    self.doc = d;
    self.pages.doc = d;
    /* a render job may still hold the old document: it renders with a stale generation
       check first, but keep the old document alive (a spike-level leak, see README). */
    (void)old;
    [self.scroll.contentView scrollToPoint:NSMakePoint(0, 0)];
    [self.scroll reflectScrolledClipView:self.scroll.contentView];
    self.window.title = path.lastPathComponent;
    [self.window setTitleWithRepresentedFilename:path];
    return YES;
}

- (void)setMagnificationTo:(CGFloat)m {
    m = MIN(kMaxMag, MAX(kMinMag, m));
    NSRect vis = self.scroll.contentView.bounds;
    NSPoint centre = NSMakePoint(NSMidX(vis), NSMidY(vis));
    [self.scroll setMagnification:m centeredAtPoint:centre];
    [self syncMagnification];
}
- (void)zoomIn:(id)sender { (void)sender; [self setMagnificationTo:self.scroll.magnification * kStep]; }
- (void)zoomOut:(id)sender { (void)sender; [self setMagnificationTo:self.scroll.magnification / kStep]; }
- (void)actualSize:(id)sender { (void)sender; [self setMagnificationTo:1]; }

- (void)openDocument:(id)sender {
    (void)sender;
    NSOpenPanel *p = [NSOpenPanel openPanel];
    p.allowedFileTypes = @[ @"pdf" ];
    if ([p runModal] == NSModalResponseOK) [self openPath:p.URL.path];
}

- (void)buildMenu {
    NSMenu *bar = [NSMenu new];
    NSMenuItem *appItem = [NSMenuItem new];
    [bar addItem:appItem];
    NSMenu *app = [NSMenu new];
    [app addItemWithTitle:@"Quit safe-pdf" action:@selector(terminate:) keyEquivalent:@"q"];
    appItem.submenu = app;

    NSMenuItem *fileItem = [NSMenuItem new];
    [bar addItem:fileItem];
    NSMenu *file = [[NSMenu alloc] initWithTitle:@"File"];
    [file addItemWithTitle:@"Open…" action:@selector(openDocument:) keyEquivalent:@"o"].target = self;
    [file addItemWithTitle:@"Close Window" action:@selector(performClose:) keyEquivalent:@"w"];
    fileItem.submenu = file;

    NSMenuItem *viewItem = [NSMenuItem new];
    [bar addItem:viewItem];
    NSMenu *view = [[NSMenu alloc] initWithTitle:@"View"];
    [view addItemWithTitle:@"Zoom In" action:@selector(zoomIn:) keyEquivalent:@"+"].target = self;
    NSMenuItem *alt = [view addItemWithTitle:@"Zoom In" action:@selector(zoomIn:) keyEquivalent:@"="];
    alt.target = self; alt.hidden = YES; alt.allowsKeyEquivalentWhenHidden = YES;
    [view addItemWithTitle:@"Zoom Out" action:@selector(zoomOut:) keyEquivalent:@"-"].target = self;
    [view addItemWithTitle:@"Actual Size" action:@selector(actualSize:) keyEquivalent:@"0"].target = self;
    viewItem.submenu = view;
    NSApp.mainMenu = bar;
}

- (void)applicationDidFinishLaunching:(NSNotification *)n {
    (void)n;
    [self buildMenu];
    NSRect frame = NSMakeRect(0, 0, 820, 1000);
    self.window = [[NSWindow alloc] initWithContentRect:frame
        styleMask:NSWindowStyleMaskTitled | NSWindowStyleMaskClosable |
                  NSWindowStyleMaskResizable | NSWindowStyleMaskMiniaturizable
        backing:NSBackingStoreBuffered defer:NO];
    self.window.title = @"safe-pdf";
    self.window.delegate = self;
    [self buildViewsWithFrame:self.window.contentView.bounds];
    [self.window.contentView addSubview:self.scroll];
    [self.window center];
    [self.window makeKeyAndOrderFront:nil];
    [NSApp activateIgnoringOtherApps:YES];
    if (self.initialPath) [self openPath:self.initialPath];
    else [self openDocument:nil];
    NSLog(@"startup to first window: %.0f ms", nowMs() - gProcessStartMs);
}
- (void)windowDidChangeBackingProperties:(NSNotification *)n { (void)n; [self.pages setNeedsDisplay:YES]; }
- (BOOL)applicationShouldTerminateAfterLastWindowClosed:(NSApplication *)a { (void)a; return YES; }
@end

/* ---------- self-test ---------- */

static BOOL writePNG(CGImageRef img, NSString *path) {
    NSBitmapImageRep *rep = [[NSBitmapImageRep alloc] initWithCGImage:img];
    NSData *png = [rep representationUsingType:NSBitmapImageFileTypePNG properties:@{}];
    return [png writeToFile:path atomically:YES];
}

/* Draws `view`'s `rect` (points) into a bitmap of `scale` pixels per point, off screen. */
static BOOL snapshot(NSView *view, NSRect rect, CGFloat scale, NSString *path) {
    NSBitmapImageRep *rep = [[NSBitmapImageRep alloc]
        initWithBitmapDataPlanes:NULL pixelsWide:(NSInteger)(rect.size.width * scale)
        pixelsHigh:(NSInteger)(rect.size.height * scale) bitsPerSample:8 samplesPerPixel:4
        hasAlpha:YES isPlanar:NO colorSpaceName:NSDeviceRGBColorSpace bytesPerRow:0 bitsPerPixel:0];
    rep.size = rect.size;
    [view cacheDisplayInRect:rect toBitmapImageRep:rep];
    NSData *png = [rep representationUsingType:NSBitmapImageFileTypePNG properties:@{}];
    return [png writeToFile:path atomically:YES];
}

/* Runs the main run loop until `pages` has no render in flight (max `limit` s). */
static double pump(PageView *pages, double limit) {
    double t0 = nowMs();
    do {
        [[NSRunLoop currentRunLoop] runMode:NSDefaultRunLoopMode
                                 beforeDate:[NSDate dateWithTimeIntervalSinceNow:0.005]];
    } while ([pages pendingCount] > 0 && nowMs() - t0 < limit * 1000);
    return nowMs() - t0;
}

static int selfTest(NSString *dir, NSString *path) {
    [[NSFileManager defaultManager] createDirectoryAtPath:dir withIntermediateDirectories:YES
                                               attributes:nil error:NULL];
    NSMutableString *log = [NSMutableString string];
    int failures = 0;
    #define LOG(...) do { NSString *s_ = [NSString stringWithFormat:__VA_ARGS__]; \
        [log appendFormat:@"%@\n", s_]; fprintf(stderr, "%s\n", s_.UTF8String); } while (0)
    #define CHECK(c, ...) do { if (!(c)) { failures++; LOG(@"FAIL: " __VA_ARGS__); } } while (0)

    LOG(@"startup (process start to core initialised): %.1f ms", nowMs() - gProcessStartMs);
    double t0 = nowMs();
    char *err = NULL;
    safepdf_doc *doc = safepdf_open(path.fileSystemRepresentation, &err);
    LOG(@"open %@: %.1f ms", path.lastPathComponent, nowMs() - t0);
    if (!doc) { LOG(@"FAIL: open: %s", err); return 1; }
    size_t n = safepdf_page_count(doc);
    double w = 0, h = 0;
    safepdf_page_size(doc, 0, &w, &h);
    LOG(@"pages: %zu; page 1: %.2f x %.2f pt", n, w, h);
    CHECK(safepdf_page_size(doc, n, &w, &h) == -1, @"page_size out of range accepted");

    /* error path */
    char *e2 = NULL;
    CHECK(safepdf_open("/nonexistent/x.pdf", &e2) == NULL && e2 != NULL, @"open of a missing file");
    LOG(@"missing-file error text: %s", e2 ? e2 : "(none)");
    free(e2);
    safepdf_image bad; char *e3 = NULL;
    CHECK(safepdf_render(doc, n, 1, 1, &bad, &e3) == -1 && e3, @"render out of range accepted");
    LOG(@"out-of-range render error text: %s", e3 ? e3 : "(none)");
    free(e3);

    /* C API: page 1 at 1x and 2x, then every page (max 10) at 2x */
    for (int s = 1; s <= 2; s++) {
        safepdf_image img;
        double r0 = nowMs();
        int rc = safepdf_render(doc, 0, (uint32_t)s, 1, &img, &err);
        double ms = nowMs() - r0;
        CHECK(rc == 0, @"render page 1 at %dx: %s", s, err);
        if (rc != 0) continue;
        LOG(@"C API render page 1 at %dx: %zu x %zu px, %.1f ms", s, img.width, img.height, ms);
        CHECK(img.width == (size_t)llround(w * s) && img.height == (size_t)llround(h * s),
              @"image size %zu x %zu at %dx", img.width, img.height, s);
        CGImageRef ci = imageFromRender(&img);
        CHECK(writePNG(ci, [dir stringByAppendingFormat:@"/capi-page1-%dx.png", s]), @"write png");
        CGImageRelease(ci);
    }
    size_t m = n < 10 ? n : 10;
    double total = 0, worst = 0;
    for (size_t i = 0; i < m; i++) {
        safepdf_image img;
        double r0 = nowMs();
        if (safepdf_render(doc, i, 2, 1, &img, &err) != 0) { LOG(@"FAIL: page %zu: %s", i + 1, err); failures++; continue; }
        double ms = nowMs() - r0;
        total += ms; worst = MAX(worst, ms);
        safepdf_image_free(&img);
    }
    LOG(@"C API render at 2x, pages 1-%zu: mean %.1f ms/page, worst %.1f ms", m, total / m, worst);

    /* The real view hierarchy, off screen (no window): scroll view + page view. */
    Controller *c = [Controller new];
    NSRect frame = NSMakeRect(0, 0, 700, 900);
    [c buildViewsWithFrame:frame];
    c.doc = doc;
    c.pages.doc = doc;
    __block double firstMs = -1;
    __block double requested = nowMs();
    c.pages.onRender = ^(RenderResult *res) {
        if (firstMs < 0 && res.image) firstMs = nowMs() - requested;
        LOG(@"  view render page %ld at %.3f px/pt: %.1f ms on the render thread%@",
            (long)res.page + 1, res.scaleKey / 1000.0, res.ms,
            res.error ? [@" error: " stringByAppendingString:res.error] : @"");
    };
    [c.scroll layoutSubtreeIfNeeded];
    for (int s = 1; s <= 2; s++) {
        c.pages.scaleOverride = s;
        firstMs = -1; requested = nowMs();
        [c.pages updateForVisibleRect:c.pages.visibleRect];
        double waited = pump(c.pages, 60);
        LOG(@"view at %dx: first page visible after %.1f ms, all visible pages after %.1f ms", s, firstMs, waited);
        CHECK(snapshot(c.scroll, c.scroll.bounds, s, [dir stringByAppendingFormat:@"/view-top-%dx.png", s]),
              @"snapshot %dx", s);
    }
    /* zoom: two Cmd+ steps (x1.5625), then render again at 2x backing */
    [c setMagnificationTo:kStep * kStep];
    LOG(@"magnification after two zoom-in steps: %.4f", c.scroll.magnification);
    CHECK(fabs(c.scroll.magnification - kStep * kStep) < 1e-6, @"magnification not applied");
    requested = nowMs(); firstMs = -1;
    [c.pages updateForVisibleRect:c.pages.visibleRect];
    LOG(@"zoomed re-render waited %.1f ms", pump(c.pages, 60));
    CHECK(snapshot(c.scroll, c.scroll.bounds, 2, [dir stringByAppendingString:@"/view-zoom-2x.png"]), @"snapshot zoom");
    /* scroll: to the top of page 2 (or the bottom of page 1) */
    [c setMagnificationTo:1];
    NSRect target = n > 1 ? [c.pages pageRect:1] : [c.pages pageRect:0];
    NSPoint p = NSMakePoint(c.scroll.contentView.bounds.origin.x, target.origin.y - kGap);
    [c.scroll.contentView scrollToPoint:[c.scroll.contentView constrainBoundsRect:
        (NSRect){p, c.scroll.contentView.bounds.size}].origin];
    [c.scroll reflectScrolledClipView:c.scroll.contentView];
    LOG(@"scrolled to y = %.1f pt (page 2 top = %.1f)", c.scroll.contentView.bounds.origin.y, target.origin.y);
    [c.pages updateForVisibleRect:c.pages.visibleRect];
    LOG(@"scrolled re-render waited %.1f ms", pump(c.pages, 60));
    CHECK(snapshot(c.scroll, c.scroll.bounds, 2, [dir stringByAppendingString:@"/view-scroll-2x.png"]), @"snapshot scroll");

    LOG(@"total self-test time: %.0f ms; failures: %d", nowMs() - gProcessStartMs, failures);
    [log writeToFile:[dir stringByAppendingString:@"/timings.txt"] atomically:YES
            encoding:NSUTF8StringEncoding error:NULL];
    return failures ? 1 : 0;
}

int main(int argc, const char *argv[]) {
    gProcessStartMs = nowMs();
    @autoreleasepool {
        const char *st = getenv("SAFEPDF_MACOS_SELFTEST");
        NSApplication *app = [NSApplication sharedApplication];
        if (st && *st) {
            /* Never become a UI app: no Dock icon, no activation, no window. */
            [app setActivationPolicy:NSApplicationActivationPolicyProhibited];
        } else {
            [app setActivationPolicy:NSApplicationActivationPolicyRegular];
        }
        if (safepdf_init() != 0) { fprintf(stderr, "safe-pdf: core initialisation failed\n"); return 1; }
        NSString *path = argc > 1 ? [NSString stringWithUTF8String:argv[1]] : nil;
        if (st && *st) {
            if (!path) { fprintf(stderr, "self-test needs a PDF path\n"); return 2; }
            exit(selfTest([NSString stringWithUTF8String:st], path));
        }
        Controller *c = [Controller new];
        c.initialPath = path;
        app.delegate = c;
        [app run];
    }
    return 0;
}
