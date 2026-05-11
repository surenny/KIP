/* Blueprint Mobile Enhancements — TOC overlay, dep-graph pan-zoom, MathJax tweaks */
(function() {
  'use strict';

  var MOBILE_BREAKPOINT = 768;

  function isMobile() {
    return window.innerWidth <= MOBILE_BREAKPOINT;
  }

  /* ── 1. TOC slide-in overlay ──
   *
   * Overrides the simple jQuery .toggle() in plastex.js with a proper
   * slide-in drawer + backdrop. Only activates on narrow screens.
   */
  function initTocOverlay($) {
    if (!isMobile()) return;

    var $toc = $('nav.toc');
    if (!$toc.length) return;

    // Undo any inline display style that plastex.js .toggle() may have set
    $toc.css('display', '');

    var $backdrop = $('<div class="mobile-toc-backdrop">');
    $('body').append($backdrop);

    function openToc() {
      $toc.addClass('mobile-open');
      $backdrop.addClass('visible');
      $('body').addClass('mobile-toc-active');
    }

    function closeToc() {
      $toc.removeClass('mobile-open');
      $backdrop.removeClass('visible');
      $('body').removeClass('mobile-toc-active');
    }

    function toggleToc() {
      if ($toc.hasClass('mobile-open')) {
        closeToc();
      } else {
        openToc();
      }
    }

    // Override the plastex.js click handler
    $('#toc-toggle').off('click').on('click', function(e) {
      e.stopPropagation();
      toggleToc();
    });

    $backdrop.on('click', closeToc);

    // Close after navigating
    $toc.on('click', 'a', function() {
      closeToc();
    });

    // Close on Escape
    $(document).on('keydown', function(e) {
      if (e.key === 'Escape' && $toc.hasClass('mobile-open')) {
        closeToc();
      }
    });
  }


  /* ── 2. Dependency graph pan-zoom ──
   *
   * Uses d3.zoom (included in the d3 v5 full bundle already loaded by
   * dep_graph pages) to enable pinch-zoom and pan on the SVG graph.
   * Works on both desktop (scroll-wheel) and mobile (touch gestures).
   */
  function initGraphPanZoom() {
    var graphEl = document.getElementById('graph');
    if (!graphEl || typeof d3 === 'undefined' || typeof d3.zoom !== 'function') return;

    var observer = new MutationObserver(function(mutations, obs) {
      var svg = graphEl.querySelector('svg');
      if (!svg) return;
      obs.disconnect();
      // Small delay to let graphviz finish its post-render callbacks
      setTimeout(function() { enablePanZoom(svg); }, 200);
    });
    observer.observe(graphEl, { childList: true, subtree: true });
  }

  function enablePanZoom(svgEl) {
    var svgSel = d3.select(svgEl);
    var g = svgSel.select('g');
    if (!g.node()) return;

    var zoom = d3.zoom()
      .scaleExtent([0.2, 6])
      .on('zoom', function() {
        // d3 v5 API: transform is on d3.event, not the callback argument
        g.attr('transform', d3.event.transform);
      });

    svgSel.call(zoom);

    // Disable double-click zoom to prevent accidental triggers on mobile
    svgSel.on('dblclick.zoom', null);

    // Let SVG fill its container instead of using fixed width/height
    svgEl.removeAttribute('width');
    svgEl.removeAttribute('height');
    svgEl.style.width = '100%';
    svgEl.style.height = '100%';

    // Fit initial view: reset to identity transform
    var bbox = g.node().getBBox();
    var containerW = graphEl.clientWidth;
    var containerH = graphEl.clientHeight;
    if (bbox.width > 0 && bbox.height > 0 && containerW > 0 && containerH > 0) {
      var scale = Math.min(
        containerW / bbox.width,
        containerH / bbox.height
      ) * 0.9;
      var tx = (containerW - bbox.width * scale) / 2 - bbox.x * scale;
      var ty = (containerH - bbox.height * scale) / 2 - bbox.y * scale;
      svgSel.call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
    }
  }


  /* ── 3. MathJax mobile tweaks ── */
  function initMathJaxTweaks() {
    if (!isMobile()) return;

    // Disable MathJax context menu on mobile (prevents long-press conflicts)
    if (window.MathJax && window.MathJax.startup && window.MathJax.startup.promise) {
      window.MathJax.startup.promise.then(function() {
        try {
          var opts = MathJax.config.options || {};
          opts.menuOptions = opts.menuOptions || {};
          opts.menuOptions.settings = opts.menuOptions.settings || {};
          opts.menuOptions.settings.zoom = 'None';
          opts.enableMenu = false;
        } catch(e) { /* non-critical */ }
      });
    }
  }


  /* ── Init ── */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }

  function boot() {
    // jQuery may not be loaded yet on dep_graph pages (different script order)
    if (typeof jQuery !== 'undefined') {
      initTocOverlay(jQuery);
    }
    initGraphPanZoom();
    initMathJaxTweaks();
  }

})();
