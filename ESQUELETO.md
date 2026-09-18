# ESQUELETO formal en Lean 4 + Mathlib

Estado del esqueleto formal de la cadena de resultados sobre la estructura
F = (P, G) con G = SU(2). Solo definiciones y enunciados; todas las
demostraciones son `sorry`, salvo las marcadas PROBADO.

## Entorno

| Elemento | Valor |
|---|---|
| Lean | 4.34.0 (toolchain estable `leanprover/lean4:v4.34.0`) |
| Mathlib | etiqueta `v4.34.0` (commit `5ed2965256`) |
| Proyecto | Lake, `lakefile.toml`, biblioteca `Compila` |
| Archivos | `Compila/Definiciones.lean`, `Compila/Etapa1.lean`, `Compila/Etapa2.lean`, `Compila/Etapa3.lean` |

Nota sobre la instalación: en el entorno de esta sesión los hosts
`release.lean-lang.org`, `reservoir.lean-lang.org`, `cache.mathlib.org` y
`lakecache.blob.core.windows.net` están bloqueados por el proxy. El toolchain se
descargó desde GitHub Releases y se registró con `elan toolchain link`; Mathlib se
declaró por URL git y se compiló desde fuente solo la parte necesaria (no se pudo
usar `lake exe cache get`). Por eso los archivos importan módulos concretos de
Mathlib en lugar de `import Mathlib` completo (ver sección final).

PENDIENTE: tabla de resultados.
