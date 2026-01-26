/**
 * Docsify LEAN 4 Playground Plugin
 * 为 lean 代码块添加"在线运行"功能，使用 live.lean-lang.org 作为后端
 */

(function () {
  'use strict';

  // LZString 压缩库（精简版，仅包含 compressToBase64）
  var LZString = (function () {
    var keyStrBase64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=";

    function _compress(uncompressed, bitsPerChar, getCharFromInt) {
      if (uncompressed == null) return "";
      var i, value,
          context_dictionary = {},
          context_dictionaryToCreate = {},
          context_c = "",
          context_wc = "",
          context_w = "",
          context_enlargeIn = 2,
          context_dictSize = 3,
          context_numBits = 2,
          context_data = [],
          context_data_val = 0,
          context_data_position = 0,
          ii;

      for (ii = 0; ii < uncompressed.length; ii += 1) {
        context_c = uncompressed.charAt(ii);
        if (!Object.prototype.hasOwnProperty.call(context_dictionary, context_c)) {
          context_dictionary[context_c] = context_dictSize++;
          context_dictionaryToCreate[context_c] = true;
        }

        context_wc = context_w + context_c;
        if (Object.prototype.hasOwnProperty.call(context_dictionary, context_wc)) {
          context_w = context_wc;
        } else {
          if (Object.prototype.hasOwnProperty.call(context_dictionaryToCreate, context_w)) {
            if (context_w.charCodeAt(0) < 256) {
              for (i = 0; i < context_numBits; i++) {
                context_data_val = (context_data_val << 1);
                if (context_data_position == bitsPerChar - 1) {
                  context_data_position = 0;
                  context_data.push(getCharFromInt(context_data_val));
                  context_data_val = 0;
                } else {
                  context_data_position++;
                }
              }
              value = context_w.charCodeAt(0);
              for (i = 0; i < 8; i++) {
                context_data_val = (context_data_val << 1) | (value & 1);
                if (context_data_position == bitsPerChar - 1) {
                  context_data_position = 0;
                  context_data.push(getCharFromInt(context_data_val));
                  context_data_val = 0;
                } else {
                  context_data_position++;
                }
                value = value >> 1;
              }
            } else {
              value = 1;
              for (i = 0; i < context_numBits; i++) {
                context_data_val = (context_data_val << 1) | value;
                if (context_data_position == bitsPerChar - 1) {
                  context_data_position = 0;
                  context_data.push(getCharFromInt(context_data_val));
                  context_data_val = 0;
                } else {
                  context_data_position++;
                }
                value = 0;
              }
              value = context_w.charCodeAt(0);
              for (i = 0; i < 16; i++) {
                context_data_val = (context_data_val << 1) | (value & 1);
                if (context_data_position == bitsPerChar - 1) {
                  context_data_position = 0;
                  context_data.push(getCharFromInt(context_data_val));
                  context_data_val = 0;
                } else {
                  context_data_position++;
                }
                value = value >> 1;
              }
            }
            context_enlargeIn--;
            if (context_enlargeIn == 0) {
              context_enlargeIn = Math.pow(2, context_numBits);
              context_numBits++;
            }
            delete context_dictionaryToCreate[context_w];
          } else {
            value = context_dictionary[context_w];
            for (i = 0; i < context_numBits; i++) {
              context_data_val = (context_data_val << 1) | (value & 1);
              if (context_data_position == bitsPerChar - 1) {
                context_data_position = 0;
                context_data.push(getCharFromInt(context_data_val));
                context_data_val = 0;
              } else {
                context_data_position++;
              }
              value = value >> 1;
            }
          }
          context_enlargeIn--;
          if (context_enlargeIn == 0) {
            context_enlargeIn = Math.pow(2, context_numBits);
            context_numBits++;
          }
          context_dictionary[context_wc] = context_dictSize++;
          context_w = String(context_c);
        }
      }

      if (context_w !== "") {
        if (Object.prototype.hasOwnProperty.call(context_dictionaryToCreate, context_w)) {
          if (context_w.charCodeAt(0) < 256) {
            for (i = 0; i < context_numBits; i++) {
              context_data_val = (context_data_val << 1);
              if (context_data_position == bitsPerChar - 1) {
                context_data_position = 0;
                context_data.push(getCharFromInt(context_data_val));
                context_data_val = 0;
              } else {
                context_data_position++;
              }
            }
            value = context_w.charCodeAt(0);
            for (i = 0; i < 8; i++) {
              context_data_val = (context_data_val << 1) | (value & 1);
              if (context_data_position == bitsPerChar - 1) {
                context_data_position = 0;
                context_data.push(getCharFromInt(context_data_val));
                context_data_val = 0;
              } else {
                context_data_position++;
              }
              value = value >> 1;
            }
          } else {
            value = 1;
            for (i = 0; i < context_numBits; i++) {
              context_data_val = (context_data_val << 1) | value;
              if (context_data_position == bitsPerChar - 1) {
                context_data_position = 0;
                context_data.push(getCharFromInt(context_data_val));
                context_data_val = 0;
              } else {
                context_data_position++;
              }
              value = 0;
            }
            value = context_w.charCodeAt(0);
            for (i = 0; i < 16; i++) {
              context_data_val = (context_data_val << 1) | (value & 1);
              if (context_data_position == bitsPerChar - 1) {
                context_data_position = 0;
                context_data.push(getCharFromInt(context_data_val));
                context_data_val = 0;
              } else {
                context_data_position++;
              }
              value = value >> 1;
            }
          }
          context_enlargeIn--;
          if (context_enlargeIn == 0) {
            context_enlargeIn = Math.pow(2, context_numBits);
            context_numBits++;
          }
          delete context_dictionaryToCreate[context_w];
        } else {
          value = context_dictionary[context_w];
          for (i = 0; i < context_numBits; i++) {
            context_data_val = (context_data_val << 1) | (value & 1);
            if (context_data_position == bitsPerChar - 1) {
              context_data_position = 0;
              context_data.push(getCharFromInt(context_data_val));
              context_data_val = 0;
            } else {
              context_data_position++;
            }
            value = value >> 1;
          }
        }
        context_enlargeIn--;
        if (context_enlargeIn == 0) {
          context_enlargeIn = Math.pow(2, context_numBits);
          context_numBits++;
        }
      }

      value = 2;
      for (i = 0; i < context_numBits; i++) {
        context_data_val = (context_data_val << 1) | (value & 1);
        if (context_data_position == bitsPerChar - 1) {
          context_data_position = 0;
          context_data.push(getCharFromInt(context_data_val));
          context_data_val = 0;
        } else {
          context_data_position++;
        }
        value = value >> 1;
      }

      while (true) {
        context_data_val = (context_data_val << 1);
        if (context_data_position == bitsPerChar - 1) {
          context_data.push(getCharFromInt(context_data_val));
          break;
        }
        else context_data_position++;
      }
      return context_data.join('');
    }

    return {
      compressToBase64: function (input) {
        if (input == null) return "";
        var res = _compress(input, 6, function (a) { return keyStrBase64.charAt(a); });
        switch (res.length % 4) {
          default:
          case 0: return res;
          case 1: return res + "===";
          case 2: return res + "==";
          case 3: return res + "=";
        }
      }
    };
  })();

  // 生成 lean4web playground URL
  function generatePlaygroundUrl(code) {
    var compressed = LZString.compressToBase64(code);
    // lean4web 使用 codez 参数，并移除尾部的 = 号
    var codez = compressed.replace(/=*$/, '');
    return 'https://live.lean-lang.org/#codez=' + codez;
  }

  // 复制到剪贴板
  function copyToClipboard(text, button) {
    navigator.clipboard.writeText(text).then(function () {
      var originalText = button.textContent;
      button.textContent = '已复制!';
      button.classList.add('copied');
      setTimeout(function () {
        button.textContent = originalText;
        button.classList.remove('copied');
      }, 2000);
    }).catch(function (err) {
      console.error('复制失败:', err);
    });
  }

  // 为代码块添加工具栏
  function addToolbar(pre, code) {
    // 检查是否已经添加过工具栏
    if (pre.parentElement && pre.parentElement.classList.contains('lean4-code-wrapper')) {
      return;
    }

    // 创建包装器
    var wrapper = document.createElement('div');
    wrapper.className = 'lean4-code-wrapper';

    // 创建工具栏
    var toolbar = document.createElement('div');
    toolbar.className = 'lean4-toolbar';

    // 语言标签
    var langLabel = document.createElement('span');
    langLabel.className = 'lean4-lang-label';
    langLabel.textContent = 'Lean 4';

    // 按钮容器
    var buttons = document.createElement('div');
    buttons.className = 'lean4-buttons';

    // 在线运行按钮
    var runBtn = document.createElement('button');
    runBtn.className = 'lean4-btn lean4-run-btn';
    runBtn.textContent = '在线运行';
    runBtn.title = '在 live.lean-lang.org 中运行';
    runBtn.onclick = function () {
      var url = generatePlaygroundUrl(code);
      window.open(url, '_blank');
    };

    // 复制按钮
    var copyBtn = document.createElement('button');
    copyBtn.className = 'lean4-btn lean4-copy-btn';
    copyBtn.textContent = '复制';
    copyBtn.title = '复制代码到剪贴板';
    copyBtn.onclick = function () {
      copyToClipboard(code, copyBtn);
    };

    buttons.appendChild(runBtn);
    buttons.appendChild(copyBtn);
    toolbar.appendChild(langLabel);
    toolbar.appendChild(buttons);

    // 包装代码块
    pre.parentNode.insertBefore(wrapper, pre);
    wrapper.appendChild(toolbar);
    wrapper.appendChild(pre);
  }

  // 处理页面中的所有 lean 代码块
  function processLeanCodeBlocks() {
    var codeBlocks = document.querySelectorAll('pre[data-lang="lean"] code, pre code.language-lean, pre code.lang-lean');

    codeBlocks.forEach(function (codeElement) {
      var pre = codeElement.parentElement;
      if (pre && pre.tagName === 'PRE') {
        var code = codeElement.textContent || codeElement.innerText;
        addToolbar(pre, code);
      }
    });

    // 也处理没有 code 子元素的情况
    var preTags = document.querySelectorAll('pre[data-lang="lean"]');
    preTags.forEach(function (pre) {
      if (!pre.querySelector('code')) {
        var code = pre.textContent || pre.innerText;
        addToolbar(pre, code);
      }
    });
  }

  // Docsify 插件
  function lean4Plugin(hook, vm) {
    // 页面加载完成后处理代码块
    hook.doneEach(function () {
      // 延迟执行以确保 Prism 高亮完成
      setTimeout(processLeanCodeBlocks, 100);
    });
  }

  // 注册插件
  if (window.$docsify) {
    window.$docsify.plugins = (window.$docsify.plugins || []).concat(lean4Plugin);
  }

  // 导出给外部使用
  window.Lean4Playground = {
    generateUrl: generatePlaygroundUrl,
    process: processLeanCodeBlocks
  };

})();
