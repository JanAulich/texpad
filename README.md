# texpad

A tiny local LaTeX editor: a Python server on 127.0.0.1 that shows your `.tex`
files and a live PDF preview, compiled with `latexmk`.

## Requirements

- Python 3 (standard library only, nothing to install)
- A TeX distribution with `latexmk` on the PATH (TeX Live, MacTeX or MiKTeX)

## Run

```bash
python3 texpad.py /path/to/your/latex-project --port 8765
```

Then open http://127.0.0.1:8765. Use `--no-open` to skip opening the browser.

## Notes

- Binds to 127.0.0.1 only; nothing is exposed to your network.
- Marks and comments are stored locally in the project folder as
  `.texpad-marks.json` and `.texpad-annotations.json`, never in the `.tex` source.
- No license has been chosen yet.
