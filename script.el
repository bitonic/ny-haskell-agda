(defun new-invisible-intangible-overlay (start end)
  (let ((overlay (make-overlay start end)))
    (overlay-put overlay 'invisible t)
    (overlay-put overlay 'intangible t)
    overlay))

(defvar braced-blocks-overlays nil
  "Variable to store the regions we put an overlay on.")

(defun braced-blocks-hide ()
  (interactive)
  (save-excursion
    (let ((overlay-start nil)
	  (overlay-end nil))
      (while
	  (progn
	    (setq overlay-start (search-forward "-- {{{" nil t))
	    (setq overlay-end (search-forward "-- }}}" nil t))
	    overlay-start)
	(push (new-invisible-intangible-overlay (- overlay-start 7) overlay-end)
	      braced-blocks-overlays)))))

(defun braced-blocks-show ()
  (interactive)
  (while
      braced-blocks-overlays
    (let ((overlay (cdr braced-blocks-overlays)))
      (delete-overlay (car braced-blocks-overlays))
      (setq braced-blocks-overlays
	    (cdr braced-blocks-overlays)))))

(defvar code-slide-number 0
  "What slide we're in")

(defvar code-slide-before-overlay nil
  "The slide start overlay")

(defvar code-slide-after-overlay nil
  "The slide end overlay")

(defun code-slide-remove-overlays ()
  (interactive)
  (if code-slide-before-overlay
      (delete-overlay code-slide-before-overlay))
  (if code-slide-after-overlay
      (delete-overlay code-slide-after-overlay)))

(defun code-slide-install-overlays (start end)
  (code-slide-remove-overlays)
  (setq code-slide-before-overlay
	(new-invisible-intangible-overlay 0 start))
  (setq code-slide-after-overlay
	(if end
	    (new-invisible-intangible-overlay end (buffer-size))
	  nil)))

(defun code-slide-next-slide-pos ()
  (let ((pos (search-forward "-- ***" nil t)))
    (setq pos (if pos (- pos 6) nil))
    (message "Position is %s" pos)
    pos))

(defun code-slide-find-range (slide-number)
  (save-excursion
    (goto-char 0)
    (let ((slide-position nil)
	  (current-position (code-slide-next-slide-pos))
	  (current-slide-number 0))
      (while
	  (and (not slide-position)
	       current-position
	       (not (> current-slide-number slide-number)))
	(if (eq slide-number current-slide-number)
	    (setq slide-position current-position))
	(setq current-position (code-slide-next-slide-pos)
	      current-slide-number (+ current-slide-number 1)))
      (if slide-position
	  (cons slide-position current-position)
	nil))))

(defun code-slide-go-to (slide-number)
  (interactive)
  (let ((range (code-slide-find-range slide-number)))
    (if range
	(progn
	  (goto-char (car range))
	  (code-slide-install-overlays (car range) (cdr range))
	  t)
      nil)))

(defun code-slide-prev ()
  (interactive)
  (if (and (> code-slide-number 0)
	   (code-slide-go-to (- code-slide-number 1)))
      (setq code-slide-number (- code-slide-number 1))))

(defun code-slide-next ()
  (interactive)
  (if (code-slide-go-to (+ code-slide-number 1))
      (setq code-slide-number (+ code-slide-number 1))))

(add-hook 'agda2-mode-hook 'braced-blocks-hide)
(add-hook 'agda2-mode-hook
	  (lambda () (code-slide-go-to code-slide-number)))
(eval-after-load 'agda2-mode
  '(progn
     (define-key agda2-mode-map (kbd "<C-left>") 'code-slide-prev)
     (define-key agda2-mode-map (kbd "<C-right>") 'code-slide-next)))
