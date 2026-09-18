# Compila — verificación formal de `F = (P, G)` en Lean 4 + Mathlib

Proyecto Lean 4 (v4.34.0, Mathlib v4.34.0) con tres etapas:

* `Compila/Etapa1.lean` — existencia de `({∗}, SU(2))` y sus propiedades (`ETAPA1.md`).
* `Compila/Etapa2.lean` — teorema de clasificación (`ETAPA2.md`).
* `Compila/Etapa3.lean` — teorema de convergencia y corolario (`ETAPA3.md`).

Informe en lenguaje llano: `INFORME.md`.

## Compilar

```bash
# elan + Lean 4.34.0 (el fichero lean-toolchain fija la versión)
lake exe cache get   # descarga los .olean de Mathlib (si la red lo permite)
lake build           # compila Compila.Etapa1, Etapa2, Etapa3
lake env lean Test/Axioms.lean   # imprime de qué axiomas depende cada teorema principal
```

Salida esperada de `lake build`: éxito, con una única advertencia `declaration uses
'sorry'` en `Compila/Etapa1.lean` (`AdS3_image_eq_SO3`).
