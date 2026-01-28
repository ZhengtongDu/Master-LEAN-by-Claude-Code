/**
 * 证明树动画 - Modus Ponens (肯定前件)
 * 展示形式化证明的结构美
 */

(function() {
  'use strict';

  // 动画配置
  const CONFIG = {
    charDelay: 50,        // 每个字符的延迟 (ms)
    lineDrawDelay: 20,    // 推导线每个字符的延迟 (ms)
    stageDelay: 600,      // 阶段间隔 (ms)
    restartDelay: 4000,   // 完成后重新开始的延迟 (ms)
    cursorBlinkTime: 500  // 光标显示时间 (ms)
  };

  // 证明树的各个阶段
  const PROOF_STAGES = [
    // 阶段1: 前提
    {
      lines: [
        '     Γ ⊢ P → Q          Γ ⊢ P'
      ],
      delay: CONFIG.stageDelay
    },
    // 阶段2: 推导线
    {
      lines: [
        '     Γ ⊢ P → Q          Γ ⊢ P',
        '     ─────────────────────────'
      ],
      isLine: true,
      delay: CONFIG.stageDelay
    },
    // 阶段3: 结论
    {
      lines: [
        '     Γ ⊢ P → Q          Γ ⊢ P',
        '     ─────────────────────────',
        '               Γ ⊢ Q'
      ],
      delay: CONFIG.stageDelay
    },
    // 阶段4: 规则标注
    {
      lines: [
        '     Γ ⊢ P → Q          Γ ⊢ P',
        '     ───────────────────────── →E',
        '               Γ ⊢ Q'
      ],
      delay: CONFIG.stageDelay
    },
    // 阶段5: QED
    {
      lines: [
        '     Γ ⊢ P → Q          Γ ⊢ P',
        '     ───────────────────────── →E',
        '               Γ ⊢ Q',
        '',
        '              ✓ Q.E.D.'
      ],
      isQED: true,
      delay: CONFIG.restartDelay
    }
  ];

  let animationContainer = null;
  let isAnimating = false;
  let animationTimeout = null;

  /**
   * 转义 HTML 特殊字符
   */
  function escapeHtml(text) {
    return text
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;');
  }

  /**
   * 打字机效果显示文本
   */
  async function typeText(element, text, delay = CONFIG.charDelay) {
    return new Promise((resolve) => {
      let index = 0;
      const chars = [...text]; // 支持 Unicode 字符

      function typeChar() {
        if (index < chars.length) {
          element.innerHTML = escapeHtml(text.substring(0, index + 1)) +
            '<span class="typing-cursor"></span>';
          index++;
          animationTimeout = setTimeout(typeChar, delay);
        } else {
          // 移除光标，显示完整文本
          element.innerHTML = escapeHtml(text);
          animationTimeout = setTimeout(resolve, CONFIG.cursorBlinkTime);
        }
      }

      typeChar();
    });
  }

  /**
   * 绘制推导线（从中间向两边扩展的效果）
   */
  async function drawLine(element, previousLines, lineText) {
    return new Promise((resolve) => {
      const lineChars = [...lineText];
      const center = Math.floor(lineChars.length / 2);
      let left = center;
      let right = center;
      let currentLine = lineChars.map(() => ' ');

      function expandLine() {
        if (left >= 0 || right < lineChars.length) {
          if (left >= 0) {
            currentLine[left] = lineChars[left];
            left--;
          }
          if (right < lineChars.length) {
            currentLine[right] = lineChars[right];
            right++;
          }

          const displayText = previousLines.join('\n') + '\n' + currentLine.join('');
          element.innerHTML = formatProofText(displayText);
          animationTimeout = setTimeout(expandLine, CONFIG.lineDrawDelay);
        } else {
          resolve();
        }
      }

      expandLine();
    });
  }

  /**
   * 格式化证明文本，添加颜色
   */
  function formatProofText(text) {
    let formatted = escapeHtml(text);

    // 推导线着色
    formatted = formatted.replace(/(─+)/g, '<span class="proof-line">$1</span>');

    // 规则标注着色
    formatted = formatted.replace(/(→E)/g, '<span class="proof-rule">$1</span>');

    // QED 着色
    formatted = formatted.replace(/(✓ Q\.E\.D\.)/g, '<span class="proof-qed">$1</span>');

    return formatted;
  }

  /**
   * 运行证明树动画
   */
  async function runAnimation() {
    if (!animationContainer || !isAnimating) return;

    const contentElement = animationContainer.querySelector('#proof-tree-content');
    if (!contentElement) return;

    // 清空内容
    contentElement.innerHTML = '';

    let previousLines = [];

    for (let i = 0; i < PROOF_STAGES.length; i++) {
      if (!isAnimating) return;

      const stage = PROOF_STAGES[i];
      const newLines = stage.lines;

      if (stage.isLine && newLines.length > previousLines.length) {
        // 推导线特殊动画
        const lineText = newLines[newLines.length - 1];
        await drawLine(contentElement, previousLines, lineText);
        previousLines = [...newLines];
      } else {
        // 普通打字机效果
        for (let j = previousLines.length; j < newLines.length; j++) {
          if (!isAnimating) return;

          const currentText = [...previousLines, ...newLines.slice(previousLines.length, j)].join('\n');
          const newLine = newLines[j];

          if (newLine.trim() === '') {
            // 空行直接添加
            previousLines.push(newLine);
            contentElement.innerHTML = formatProofText(previousLines.join('\n'));
          } else {
            // 打字机效果
            const baseText = currentText ? currentText + '\n' : '';
            await typeLineWithBase(contentElement, baseText, newLine);
            previousLines.push(newLine);
          }
        }
      }

      // 显示完整阶段
      contentElement.innerHTML = formatProofText(previousLines.join('\n'));

      // 等待进入下一阶段
      if (isAnimating) {
        await sleep(stage.delay);
      }
    }

    // 循环播放
    if (isAnimating) {
      runAnimation();
    }
  }

  /**
   * 在已有文本基础上打字显示新行
   */
  async function typeLineWithBase(element, baseText, newLine) {
    return new Promise((resolve) => {
      let index = 0;
      const chars = [...newLine];

      function typeChar() {
        if (!isAnimating) {
          resolve();
          return;
        }

        if (index < chars.length) {
          const currentNew = newLine.substring(0, index + 1);
          element.innerHTML = formatProofText(baseText + currentNew) +
            '<span class="typing-cursor"></span>';
          index++;
          animationTimeout = setTimeout(typeChar, CONFIG.charDelay);
        } else {
          element.innerHTML = formatProofText(baseText + newLine);
          animationTimeout = setTimeout(resolve, CONFIG.cursorBlinkTime);
        }
      }

      typeChar();
    });
  }

  /**
   * 延迟函数
   */
  function sleep(ms) {
    return new Promise(resolve => {
      animationTimeout = setTimeout(resolve, ms);
    });
  }

  /**
   * 启动动画
   */
  function startAnimation() {
    animationContainer = document.getElementById('proof-tree-animation');
    if (!animationContainer) return;

    isAnimating = true;
    runAnimation();
  }

  /**
   * 停止动画
   */
  function stopAnimation() {
    isAnimating = false;
    if (animationTimeout) {
      clearTimeout(animationTimeout);
      animationTimeout = null;
    }
  }

  // docsify 插件集成
  if (window.$docsify) {
    window.$docsify.plugins = (window.$docsify.plugins || []).concat(function(hook) {
      hook.doneEach(function() {
        // 每次页面加载完成后检查是否在首页
        stopAnimation();

        // 检查是否在首页 (README.md)
        const path = window.location.hash;
        if (path === '' || path === '#/' || path === '#/README') {
          // 延迟启动，确保 DOM 已渲染
          setTimeout(startAnimation, 100);
        }
      });
    });
  } else {
    // 非 docsify 环境，直接启动
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', startAnimation);
    } else {
      startAnimation();
    }
  }
})();
