(menu-bar-mode -1)
(tool-bar-mode -1)

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

(define-prefix-command 'my-C-o-map)
(global-set-key (kbd "C-o") 'my-C-o-map)
(define-key my-C-o-map (kbd "C-v") 'agda2-compute-normalised-maybe-toplevel)
(define-key my-C-o-map (kbd "C-p") 'agda2-give)
(define-key my-C-o-map (kbd ",") 'agda2-goal-and-context)
(define-key my-C-o-map (kbd ";") 'agda2-goal-and-context-and-checked)
(define-key my-C-o-map (kbd ".") 'agda2-goal-and-context-and-inferred)
(define-key my-C-o-map (kbd "=") 'agda2-show-constraints)
(global-set-key (kbd "C-c C-v") 'agda2-compute-normalised-maybe-toplevel)
(global-set-key (kbd "C-c C-p") 'agda2-give)
(global-set-key (kbd "C-c ,")   'agda2-goal-and-context)
(global-set-key (kbd "C-c ;")   'agda2-goal-and-context-and-checked)
(global-set-key (kbd "C-c .")   'agda2-goal-and-context-and-inferred)
(global-set-key (kbd "C-c =")   'agda2-show-constraints)
(add-hook 'agda2-mode-hook
  #'(lambda () (define-key (current-local-map) (kbd "C-o") (lookup-key (current-local-map) (kbd "C-c")))))
(global-set-key (kbd "C-c C-y") (lambda() (interactive) (find-file "~/.hello.txt")))

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

(add-hook 'emacs-startup-hook
  (lambda ()
    (message "Welcome to Agda! For a list of keyboard commands, press Ctrl-c Ctrl-y.")))
