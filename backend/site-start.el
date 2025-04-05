(menu-bar-mode -1)
(tool-bar-mode -1)
(scroll-bar-mode -1)

(load-file (let ((coding-system-for-read 'utf-8)) (shell-command-to-string "agda-mode locate")))
(setq auto-mode-alist
  (append
    '(("\\.agda\\'" . agda2-mode)
      ("\\.lagda.md\\'" . agda2-mode))
    auto-mode-alist))

(setq-default indent-tabs-mode nil)

(set-terminal-parameter nil 'background-mode 'light)
(load-theme 'tsdh-light)

(custom-set-variables
  '(xterm-mouse-mode t)
  '(inhibit-startup-screen t))

(global-set-key (kbd "C-c C-v") 'agda2-compute-normalised-maybe-toplevel)
(global-set-key (kbd "C-c C-p") 'agda2-give)
(add-hook 'agda2-mode-hook
  #'(lambda () (define-key (current-local-map) (kbd "C-o") (lookup-key (current-local-map) (kbd "C-c")))))

(require 'evil)
(setq evil-default-state 'emacs)
(setq evil-want-fine-undo 't)
(evil-mode 1)

(put 'narrow-to-region 'disabled nil)

(defun narrow-to-line-range (start-line end-line)
  "Narrow buffer to lines START-LINE to END-LINE."
  (save-excursion
    (goto-line start-line)
    (beginning-of-line)
    (let ((start (point)))
      (goto-line end-line)
      (end-of-line)
      (narrow-to-region start (point)))))
