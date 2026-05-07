/* Blueprint Annotation System — server-backed comments via review API */
(function($) {
  'use strict';

  var REVIEWER_KEY = 'leanblueprint_reviewer_name';
  var TOPIC_COLORS = { review: '#E69F00', align: '#009E73', general: '#666' };

  var _statusCache = null;
  var _apiAvailable = false;

  function getReviewer() { return localStorage.getItem(REVIEWER_KEY) || ''; }
  function setReviewer(name) { localStorage.setItem(REVIEWER_KEY, name); }

  function fetchStatus() {
    return fetch('/api/status')
      .then(function(r) { if (!r.ok) throw new Error(r.status); return r.json(); })
      .then(function(data) {
        _statusCache = data.nodes || {};
        _apiAvailable = true;
        return _statusCache;
      })
      .catch(function() {
        _statusCache = {};
        _apiAvailable = false;
        return _statusCache;
      });
  }

  function postComment(nodeId, text, topic, reviewer) {
    return fetch('/api/review', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        node_id: nodeId,
        action: 'comment',
        text: text,
        topic: topic || 'general',
        reviewer: reviewer || 'Anonymous'
      })
    }).then(function(r) { return r.json(); });
  }

  function getNodeComments(nodeId) {
    if (!_statusCache || !_statusCache[nodeId]) return [];
    return _statusCache[nodeId].comments || [];
  }

  function escHtml(str) {
    var div = document.createElement('div');
    div.appendChild(document.createTextNode(str));
    return div.innerHTML;
  }

  function formatDate(dateStr) {
    if (!dateStr) return '';
    if (/^\d{4}-\d{2}-\d{2}$/.test(dateStr)) return dateStr;
    var d = new Date(dateStr);
    return isNaN(d) ? dateStr : d.toLocaleDateString();
  }

  function createIndicator(nodeId, count) {
    var $ind = $('<span class="annotation-indicator" data-for="' + nodeId + '">' +
      '<span class="ann-icon">✍</span>' +
      '<span class="ann-count">' + (count || '') + '</span>' +
      '</span>');
    if (count > 0) $ind.addClass('has-comments');
    return $ind;
  }

  function renderPanel(nodeId) {
    var comments = getNodeComments(nodeId);
    var $panel = $('<div class="annotation-panel open" data-panel-for="' + nodeId + '">');

    var $header = $('<div class="ann-panel-header">' +
      '<span class="ann-panel-title">Comments</span>' +
      '<button class="ann-panel-close">&times;</button>' +
      '</div>');
    $panel.append($header);

    var $list = $('<div class="ann-comments-list">');
    if (comments.length === 0) {
      $list.append('<div class="ann-empty">No comments yet.</div>');
    } else {
      comments.forEach(function(c) { $list.append(renderEntry(c)); });
    }
    $panel.append($list);

    var topicOpts = '<option value="general">general</option>' +
      '<option value="review">NL review</option>' +
      '<option value="align">alignment</option>';

    var disabledAttr = _apiAvailable ? '' : ' disabled';
    var $input = $('<div class="ann-input-area">' +
      '<div class="ann-input-row">' +
        '<label>Reviewer</label>' +
        '<input type="text" class="ann-author-input" placeholder="Your name" value="' + escHtml(getReviewer()) + '">' +
      '</div>' +
      '<div class="ann-input-row">' +
        '<label>Topic</label>' +
        '<select class="ann-comment-topic">' + topicOpts + '</select>' +
      '</div>' +
      '<textarea class="ann-text-input" placeholder="Write a comment..."></textarea>' +
      '<div style="overflow:hidden;margin-top:6px;">' +
        '<button class="ann-submit-btn"' + disabledAttr + '>Send</button>' +
      '</div>' +
      '<div class="ann-feedback"></div>' +
      '</div>');
    $panel.append($input);

    if (!_apiAvailable) {
      $panel.find('.ann-feedback').text('Server unavailable — comments are read-only.').show();
    }

    return $panel;
  }

  function renderEntry(c) {
    var topicColor = TOPIC_COLORS[c.topic] || TOPIC_COLORS.general;
    var $entry = $('<div class="ann-entry" style="border-left:3px solid ' + topicColor + '">');
    $entry.append('<div class="ann-entry-header">' +
      '<span class="ann-author">' +
        '<span class="ann-topic-badge" style="color:' + topicColor + '">' + escHtml(c.topic || 'general') + '</span> ' +
        escHtml(c.by || 'Anonymous') +
      '</span>' +
      '<span class="ann-time">' + formatDate(c.at) + '</span>' +
      '</div>');
    $entry.append('<div class="ann-text">' + escHtml(c.text || '') + '</div>');
    return $entry;
  }

  function refreshPanel(nodeId) {
    var $old = $('[data-panel-for="' + nodeId + '"]');
    if ($old.length && $old.hasClass('open')) {
      var $new = renderPanel(nodeId);
      $old.replaceWith($new);
    }
    refreshIndicator(nodeId);
  }

  function refreshIndicator(nodeId) {
    var count = getNodeComments(nodeId).length;
    var $ind = $('[data-for="' + nodeId + '"]');
    $ind.find('.ann-count').text(count || '');
    $ind.toggleClass('has-comments', count > 0);
    $('[id="' + nodeId + '"]').toggleClass('has-annotations', count > 0);
  }

  function bindEvents() {
    $(document).on('click', '.annotation-indicator', function(e) {
      e.stopPropagation();
      var nodeId = $(this).data('for');
      var $existing = $('[data-panel-for="' + nodeId + '"]');
      if ($existing.length) {
        if ($existing.hasClass('open')) {
          $existing.removeClass('open').slideUp(150);
        } else {
          $existing.addClass('open').slideDown(150);
        }
        return;
      }
      var $panel = renderPanel(nodeId);
      var $el = $('[id="' + nodeId + '"]').filter('[class*="_thmwrapper"]');
      if ($el.length) {
        $el.after($panel);
        $panel.hide().slideDown(200);
      }
    });

    $(document).on('click', '.ann-panel-close', function() {
      $(this).closest('.annotation-panel').removeClass('open').slideUp(150);
    });

    $(document).on('click', '.ann-submit-btn', function() {
      var $btn = $(this);
      var $panel = $btn.closest('.annotation-panel');
      var nodeId = $panel.data('panel-for');
      var text = $panel.find('.ann-text-input').val().trim();
      var topic = $panel.find('.ann-comment-topic').val();
      var reviewer = $panel.find('.ann-author-input').val().trim() || 'Anonymous';
      if (!text) return;

      $btn.prop('disabled', true).text('Sending...');
      setReviewer(reviewer);

      postComment(nodeId, text, topic, reviewer)
        .then(function(resp) {
          if (resp.error) {
            $panel.find('.ann-feedback').text('Error: ' + resp.error).show();
            $btn.prop('disabled', false).text('Send');
            return;
          }
          if (_statusCache[nodeId]) {
            _statusCache[nodeId].comments = resp.comments || [];
          }
          refreshPanel(nodeId);
        })
        .catch(function(err) {
          $panel.find('.ann-feedback').text('Network error — is the server running?').show();
          $btn.prop('disabled', false).text('Send');
        });
    });
  }

  function init() {
    fetchStatus().then(function() {
      $('[class*="_thmwrapper"]').each(function() {
        var nodeId = this.id;
        if (!nodeId || !_statusCache[nodeId]) return;

        var count = getNodeComments(nodeId).length;
        var $ind = createIndicator(nodeId, count);
        var $extras = $(this).find('> [class$="_thmheading"] .thm_header_extras').first();
        if ($extras.length) {
          $extras.append($ind);
        }
        if (count > 0) $(this).addClass('has-annotations');
      });
      bindEvents();
    });
  }

  $(document).ready(init);
})(jQuery);
