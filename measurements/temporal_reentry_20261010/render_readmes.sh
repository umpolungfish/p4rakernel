#!/usr/bin/env bash
set -euo pipefail

# Render the canonical README sources with the project Shavian font.
readme_kernel_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
readme_docs_root="$(dirname -- "$readme_kernel_root")/ig-docs"
readme_render_dir="$(mktemp -d "$readme_docs_root/.readme-render.XXXXXX")"
trap 'rm -rf -- "$readme_render_dir"' EXIT

cat > "$readme_render_dir/readme_symbols.tex" <<'TEX'
\newunicodechar{⊢}{{\igprimfont\char"22A2}}
\newunicodechar{⊣}{{\igprimfont\char"22A3}}
\newunicodechar{≻}{{\igprimfont\char"227B}}
\newunicodechar{≺}{{\igprimfont\char"227A}}
\newunicodechar{⋈}{{\igprimfont\char"22C8}}
\newunicodechar{∋}{{\igprimfont\char"220B}}
\newunicodechar{⊞}{{\igprimfont\char"229E}}
\newunicodechar{⊡}{{\igprimfont\char"22A1}}
TEX

for readme_name in p4rakernel p4ramill; do
  readme_source="$readme_kernel_root/README.md"
  if [[ "$readme_name" == p4ramill ]]; then
    readme_source="$readme_kernel_root/p4ramill/README.md"
  fi
  readme_tex="$readme_render_dir/${readme_name}_readme.tex"
  latextiler convert "$readme_source" -F latex --force --font-size 12 -o "$readme_tex"
  # latextiler's preamble selects Everson Mono for Shavian. ltx preserves an
  # existing shavfont definition, so select Trabajo before its compilation.
  sed -i 's/\\newfontfamily\\shavfont\[Scale=1.0\]{Everson Mono}/\\newfontfamily\\shavfont[Scale=1.0]{Trabajo}/' "$readme_tex"
  # The converter emits a bare top command for the affirmative glyph.
  sed -i 's/\\top/$\\top$/g' "$readme_tex"
  awk -v symbols="$readme_render_dir/readme_symbols.tex" '
    /^\\begin\{document\}/ {
      while ((getline line < symbols) > 0) print line
      close(symbols)
    }
    { print }
  ' "$readme_tex" > "$readme_render_dir/patched.tex"
  mv -- "$readme_render_dir/patched.tex" "$readme_tex"
  ltx "$readme_tex" --font-size 12 -o "$readme_docs_root/${readme_name}_readme.pdf"
  pdftotext -layout "$readme_docs_root/${readme_name}_readme.pdf" \
    "$readme_docs_root/${readme_name}_readme.pdf.txt"
done
