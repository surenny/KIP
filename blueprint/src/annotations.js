/* Blueprint Annotation System — localStorage-based comments for blueprint pages */
(function($) {
  'use strict';

  var STORAGE_KEY = 'blueprint_annotations';
  var AUTHOR_KEY = 'blueprint_annotations_author';

  var ANNOTATABLE_SELECTORS = [
    '[class$="_thmwrapper"]',
    '.proof_wrapper',
    '.main-text > p',
    '[class$="_thmcontent"] > p'
  ];

  // ── AnnotationStore ──

  var AnnotationStore = {
    _data: null,

    load: function() {
      if (this._data) return this._data;
      try {
        var raw = localStorage.getItem(STORAGE_KEY);
        this._data = raw ? JSON.parse(raw) : { version: 1, annotations: {} };
      } catch(e) {
        this._data = { version: 1, annotations: {} };
      }
      return this._data;
    },

    save: function() {
      try {
        localStorage.setItem(STORAGE_KEY, JSON.stringify(this._data));
      } catch(e) { /* quota exceeded — silent */ }
    },

    getForElement: function(elId) {
      var data = this.load();
      return (data.annotations[elId] || []).slice();
    },

    countForElement: function(elId) {
      var data = this.load();
      return (data.annotations[elId] || []).length;
    },

    totalCount: function() {
      var data = this.load();
      var n = 0;
      for (var k in data.annotations) n += data.annotations[k].length;
      return n;
    },

    addComment: function(elId, text, author) {
      var data = this.load();
      if (!data.annotations[elId]) data.annotations[elId] = [];
      var comment = {
        id: 'ann_' + this._uuid(),
        text: text,
        author: author || 'Anonymous',
        created: new Date().toISOString(),
        modified: null,
        resolved: false
      };
      data.annotations[elId].push(comment);
      this.save();
      return comment;
    },

    editComment: function(elId, commentId, newText) {
      var list = this.load().annotations[elId] || [];
      for (var i = 0; i < list.length; i++) {
        if (list[i].id === commentId) {
          list[i].text = newText;
          list[i].modified = new Date().toISOString();
          this.save();
          return list[i];
        }
      }
      return null;
    },

    deleteComment: function(elId, commentId) {
      var data = this.load();
      var list = data.annotations[elId] || [];
      data.annotations[elId] = list.filter(function(c) { return c.id !== commentId; });
      if (data.annotations[elId].length === 0) delete data.annotations[elId];
      this.save();
    },

    toggleResolved: function(elId, commentId) {
      var list = this.load().annotations[elId] || [];
      for (var i = 0; i < list.length; i++) {
        if (list[i].id === commentId) {
          list[i].resolved = !list[i].resolved;
          this.save();
          return list[i];
        }
      }
      return null;
    },

    exportJSON: function() {
      var data = this.load();
      var enriched = { version: data.version, annotations: {} };
      for (var elId in data.annotations) {
        var $el = $('[data-annotation-id="' + elId + '"]');
        var context = _buildContext($el, elId);
        enriched.annotations[elId] = {
          context: context,
          comments: data.annotations[elId]
        };
      }
      return JSON.stringify(enriched, null, 2);
    },

    importJSON: function(jsonStr) {
      try {
        var incoming = JSON.parse(jsonStr);
        if (!incoming.annotations) return { added: 0, error: null };
        var data = this.load();
        var added = 0;
        for (var elId in incoming.annotations) {
          var entry = incoming.annotations[elId];
          var comments = Array.isArray(entry) ? entry : (entry.comments || []);
          if (!data.annotations[elId]) data.annotations[elId] = [];
          var existing = {};
          data.annotations[elId].forEach(function(c) { existing[c.id] = true; });
          comments.forEach(function(c) {
            if (!existing[c.id]) {
              data.annotations[elId].push(c);
              added++;
            }
          });
        }
        this.save();
        return { added: added, error: null };
      } catch(e) {
        return { added: 0, error: e.message };
      }
    },

    _uuid: function() {
      return 'xxxx-xxxx'.replace(/x/g, function() {
        return (Math.random() * 16 | 0).toString(16);
      }) + '-' + Date.now().toString(36);
    }
  };

  function _buildContext($el, elId) {
    var ctx = { id: elId, page: window.location.pathname.split('/').pop() || 'index.html' };

    if (!$el.length) return ctx;

    var wrapper = $el.closest('[class$="_thmwrapper"]');
    if (wrapper.length) {
      var caption = wrapper.find('[class$="_thmcaption"]').first().text().trim();
      var label = wrapper.find('[class$="_thmlabel"]').first().text().trim();
      ctx.type = caption || 'Statement';
      ctx.label = label;
      ctx.title = (caption && label) ? caption + ' ' + label : (caption || label || '');
      var content = wrapper.find('[class$="_thmcontent"]').first().text().trim();
      ctx.excerpt = content.substring(0, 120).replace(/\s+/g, ' ');
      if (content.length > 120) ctx.excerpt += '...';
      return ctx;
    }

    if ($el.hasClass('proof_wrapper')) {
      ctx.type = 'Proof';
      var prev = $el.prev('[class$="_thmwrapper"]');
      if (prev.length) {
        var pc = prev.find('[class$="_thmcaption"]').first().text().trim();
        var pl = prev.find('[class$="_thmlabel"]').first().text().trim();
        ctx.title = 'Proof of ' + ((pc && pl) ? pc + ' ' + pl : (pc || pl || ''));
      }
      return ctx;
    }

    ctx.type = 'Paragraph';
    var text = $el.text().trim();
    ctx.excerpt = text.substring(0, 120).replace(/\s+/g, ' ');
    if (text.length > 120) ctx.excerpt += '...';

    var section = $el.closest('[id^="sec:"]');
    if (section.length) {
      ctx.section = section.find('h1,h2,h3,h4').first().text().trim() || section.attr('id');
    }
    return ctx;
  }

  // ── Stable ID assignment ──

  function getPageName() {
    var path = window.location.pathname;
    var parts = path.split('/');
    var file = parts[parts.length - 1] || 'index';
    return file.replace(/\.html$/, '');
  }

  function findNearestIdAncestor(el) {
    var node = el.parentElement;
    while (node) {
      if (node.id) return node.id;
      node = node.parentElement;
    }
    return 'root';
  }

  function assignAnnotationIds() {
    var page = getPageName();
    $(ANNOTATABLE_SELECTORS.join(',')).each(function() {
      var el = this;
      if (el.id) {
        el.setAttribute('data-annotation-id', el.id);
      } else {
        var ancestor = findNearestIdAncestor(el);
        var siblings = $(el).parent().children(el.tagName);
        var idx = siblings.index(el);
        var genId = page + '--' + ancestor + '--p' + idx;
        el.setAttribute('data-annotation-id', genId);
      }
    });
  }

  // ── Author helpers ──

  function getAuthor() {
    return localStorage.getItem(AUTHOR_KEY) || '';
  }

  function setAuthor(name) {
    localStorage.setItem(AUTHOR_KEY, name);
  }

  // ── UI rendering ──

  var showResolved = false;

  function createIndicator(annId, count) {
    var $ind = $('<span class="annotation-indicator" data-for="' + annId + '">' +
      '<span class="ann-icon">✍</span>' +
      '<span class="ann-count">' + (count || '') + '</span>' +
      '</span>');
    if (count > 0) $ind.addClass('has-comments');
    return $ind;
  }

  function formatTime(iso) {
    if (!iso) return '';
    var d = new Date(iso);
    return d.toLocaleDateString() + ' ' + d.toLocaleTimeString([], {hour:'2-digit', minute:'2-digit'});
  }

  function renderPanel(annId) {
    var comments = AnnotationStore.getForElement(annId);

    var $panel = $('<div class="annotation-panel open" data-panel-for="' + annId + '">');

    // Header
    var $header = $('<div class="ann-panel-header">' +
      '<span class="ann-panel-title">Comments</span>' +
      '<button class="ann-panel-close">&times;</button>' +
      '</div>');
    $panel.append($header);

    // Print label (visible only in print)
    $panel.append('<div class="ann-print-label">Comments:</div>');

    // Comments list
    var $list = $('<div class="ann-comments-list">');
    if (comments.length === 0) {
      $list.append('<div class="ann-empty">No comments yet.</div>');
    } else {
      var hasVisiblePrint = false;
      comments.forEach(function(c) {
        if (c.resolved && !showResolved) {
          hasVisiblePrint = true; // still exists for print
          var $entry = renderEntry(annId, c);
          $entry.css('display', 'none').addClass('ann-hidden-resolved');
          $list.append($entry);
          return;
        }
        hasVisiblePrint = true;
        $list.append(renderEntry(annId, c));
      });
      if (hasVisiblePrint) $panel.addClass('has-print-comments');
    }
    $panel.append($list);

    // Input area
    var $input = $('<div class="ann-input-area">' +
      '<div class="ann-input-row">' +
        '<label>Author</label>' +
        '<input type="text" class="ann-author-input" placeholder="Your name" value="' + escHtml(getAuthor()) + '">' +
      '</div>' +
      '<textarea class="ann-text-input" placeholder="Write a comment..."></textarea>' +
      '<div style="overflow:hidden;margin-top:6px;">' +
        '<button class="ann-submit-btn">Add Comment</button>' +
      '</div>' +
      '</div>');
    $panel.append($input);

    return $panel;
  }

  function renderEntry(annId, c) {
    var $entry = $('<div class="ann-entry" data-comment-id="' + c.id + '">');
    if (c.resolved) $entry.addClass('resolved');

    var timeStr = formatTime(c.modified || c.created);
    $entry.append('<div class="ann-entry-header">' +
      '<span class="ann-author">' + escHtml(c.author) + '</span>' +
      '<span class="ann-time">' + timeStr + '</span>' +
      '</div>');
    $entry.append('<div class="ann-text">' + escHtml(c.text) + '</div>');

    var $actions = $('<div class="ann-actions">');
    var resLabel = c.resolved ? 'Unresolve' : 'Resolve';
    var resCls = c.resolved ? ' is-resolved' : '';
    $actions.append('<button class="ann-resolve-btn' + resCls + '" data-el="' + annId + '" data-cid="' + c.id + '">' + resLabel + '</button>');
    $actions.append('<button class="ann-edit-btn" data-el="' + annId + '" data-cid="' + c.id + '">Edit</button>');
    $actions.append('<button class="ann-delete-btn" data-el="' + annId + '" data-cid="' + c.id + '">Delete</button>');
    $entry.append($actions);

    return $entry;
  }

  function refreshPanel(annId) {
    var $old = $('[data-panel-for="' + annId + '"]');
    if ($old.length && $old.hasClass('open')) {
      var $new = renderPanel(annId);
      $old.replaceWith($new);
    }
    refreshIndicator(annId);
    refreshToolbar();
  }

  function refreshIndicator(annId) {
    var count = AnnotationStore.countForElement(annId);
    var $ind = $('[data-for="' + annId + '"]');
    $ind.find('.ann-count').text(count || '');
    $ind.toggleClass('has-comments', count > 0);
    // highlight the element
    $('[data-annotation-id="' + annId + '"]').toggleClass('has-annotations', count > 0);
  }

  function refreshToolbar() {
    var total = AnnotationStore.totalCount();
    $('#annotation-toolbar .ann-toolbar-badge').text(total);
  }

  // ── Toolbar ──

  function createToolbar() {
    var total = AnnotationStore.totalCount();
    var $tb = $('<div id="annotation-toolbar">' +
      '<div class="ann-toolbar-main">' +
        '<span class="ann-toolbar-badge">' + total + '</span> annotations ' +
        '<button class="ann-export-btn" title="Export">Export</button>' +
        '<button class="ann-import-btn" title="Import">Import</button>' +
      '</div>' +
      '<div class="ann-toolbar-options">' +
        '<label><input type="checkbox" class="ann-show-resolved-chk"> Show resolved</label>' +
      '</div>' +
      '</div>');
    $('body').append($tb);
  }

  // ── Event handlers ──

  function bindEvents() {
    // Toggle panel
    $(document).on('click', '.annotation-indicator', function(e) {
      e.stopPropagation();
      var annId = $(this).data('for');
      var $existing = $('[data-panel-for="' + annId + '"]');
      if ($existing.length) {
        if ($existing.hasClass('open')) {
          $existing.removeClass('open').slideUp(150);
        } else {
          $existing.addClass('open').slideDown(150);
        }
        return;
      }
      // Create new panel
      var $panel = renderPanel(annId);
      var $el = $('[data-annotation-id="' + annId + '"]');
      $el.after($panel);
      $panel.hide().slideDown(200);
    });

    // Close panel
    $(document).on('click', '.ann-panel-close', function() {
      $(this).closest('.annotation-panel').removeClass('open').slideUp(150);
    });

    // Submit comment
    $(document).on('click', '.ann-submit-btn', function() {
      var $panel = $(this).closest('.annotation-panel');
      var annId = $panel.data('panel-for');
      var text = $panel.find('.ann-text-input').val().trim();
      var author = $panel.find('.ann-author-input').val().trim() || 'Anonymous';
      if (!text) return;
      setAuthor(author);
      AnnotationStore.addComment(annId, text, author);
      refreshPanel(annId);
    });

    // Resolve toggle
    $(document).on('click', '.ann-resolve-btn', function() {
      var annId = $(this).data('el');
      var cid = $(this).data('cid');
      AnnotationStore.toggleResolved(annId, cid);
      refreshPanel(annId);
    });

    // Edit
    $(document).on('click', '.ann-edit-btn', function() {
      var $entry = $(this).closest('.ann-entry');
      var annId = $(this).data('el');
      var cid = $(this).data('cid');
      var currentText = $entry.find('.ann-text').text();
      $entry.find('.ann-text').replaceWith(
        '<textarea class="ann-edit-textarea">' + escHtml(currentText) + '</textarea>' +
        '<div class="ann-edit-actions">' +
          '<button class="ann-save-btn" data-el="' + annId + '" data-cid="' + cid + '">Save</button>' +
          '<button class="ann-cancel-btn" data-el="' + annId + '">Cancel</button>' +
        '</div>'
      );
      $entry.find('.ann-actions').hide();
    });

    // Save edit
    $(document).on('click', '.ann-save-btn', function() {
      var annId = $(this).data('el');
      var cid = $(this).data('cid');
      var newText = $(this).closest('.ann-entry').find('.ann-edit-textarea').val().trim();
      if (newText) AnnotationStore.editComment(annId, cid, newText);
      refreshPanel(annId);
    });

    // Cancel edit
    $(document).on('click', '.ann-cancel-btn', function() {
      var annId = $(this).data('el');
      refreshPanel(annId);
    });

    // Delete
    $(document).on('click', '.ann-delete-btn', function() {
      if (!confirm('Delete this comment?')) return;
      var annId = $(this).data('el');
      var cid = $(this).data('cid');
      AnnotationStore.deleteComment(annId, cid);
      refreshPanel(annId);
    });

    // Show resolved toggle
    $(document).on('change', '.ann-show-resolved-chk', function() {
      showResolved = $(this).is(':checked');
      // Re-render all open panels
      $('.annotation-panel.open').each(function() {
        var annId = $(this).data('panel-for');
        refreshPanel(annId);
      });
      // Restore checkbox state
      $('.ann-show-resolved-chk').prop('checked', showResolved);
    });

    // Export
    $(document).on('click', '.ann-export-btn', function() {
      var json = AnnotationStore.exportJSON();
      var blob = new Blob([json], { type: 'application/json' });
      var url = URL.createObjectURL(blob);
      var a = document.createElement('a');
      var date = new Date().toISOString().slice(0,10);
      a.href = url;
      a.download = 'blueprint-annotations-' + date + '.json';
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    });

    // Import
    $(document).on('click', '.ann-import-btn', function() {
      var input = document.createElement('input');
      input.type = 'file';
      input.accept = '.json';
      input.onchange = function(e) {
        var file = e.target.files[0];
        if (!file) return;
        var reader = new FileReader();
        reader.onload = function(ev) {
          var result = AnnotationStore.importJSON(ev.target.result);
          if (result.error) {
            alert('Import failed: ' + result.error);
          } else {
            alert('Imported ' + result.added + ' new comment(s).');
            // Refresh all indicators
            $('[data-annotation-id]').each(function() {
              refreshIndicator($(this).data('annotation-id'));
            });
            refreshToolbar();
          }
        };
        reader.readAsText(file);
      };
      input.click();
    });
  }

  // ── Print preparation ──

  function preparePrint() {
    // Before printing, inject panels for elements with comments so they appear in print
    window.addEventListener('beforeprint', function() {
      $('[data-annotation-id]').each(function() {
        var annId = $(this).data('annotation-id');
        var count = AnnotationStore.countForElement(annId);
        if (count === 0) return;
        var $existing = $('[data-panel-for="' + annId + '"]');
        if ($existing.length === 0) {
          var $panel = renderPanel(annId);
          $panel.removeClass('open').addClass('has-print-comments');
          $(this).after($panel);
        } else {
          $existing.addClass('has-print-comments');
        }
      });
    });
  }

  // ── Helpers ──

  function escHtml(str) {
    var div = document.createElement('div');
    div.appendChild(document.createTextNode(str));
    return div.innerHTML;
  }

  // ── Init ──

  function init() {
    assignAnnotationIds();

    // Insert indicators
    $('[data-annotation-id]').each(function() {
      var $el = $(this);
      var annId = $el.data('annotation-id');
      var count = AnnotationStore.countForElement(annId);
      var $ind = createIndicator(annId, count);

      // For theorem-like wrappers: put in thm_header_extras
      var $extras = $el.find('> [class$="_thmheading"] .thm_header_extras').first();
      if ($extras.length) {
        $extras.append($ind);
      }
      // For proof wrappers: put in proof_heading
      else if ($el.hasClass('proof_wrapper')) {
        $el.find('> .proof_heading').first().append($ind);
      }
      // For paragraphs: float to the right
      else if ($el.is('p')) {
        $el.css('position', 'relative');
        $ind.addClass('ann-indicator-float');
        $el.append($ind);
      }

      if (count > 0) $el.addClass('has-annotations');
    });

    createToolbar();
    bindEvents();
    preparePrint();
  }

  // Run on DOM ready
  $(document).ready(function() {
    init();
  });

})(jQuery);
