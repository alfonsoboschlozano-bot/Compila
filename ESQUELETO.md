# ESQUELETO formal en Lean 4 + Mathlib

Estado del esqueleto formal de la cadena de resultados sobre la estructura
F = (P, G) con G = SU(2). Solo definiciones y enunciados. Todas las
demostraciones son `sorry`, salvo las cuatro triviales marcadas **PROBADO**.

## Entorno

| Elemento | Valor |
|---|---|
| Lean | 4.34.0 (toolchain estable `leanprover/lean4:v4.34.0`) |
| Mathlib | etiqueta `v4.34.0` (commit `5ed2965256`) |
| Proyecto | Lake (`lakefile.toml`), biblioteca `Compila`, raíz `Compila.lean` |
| Archivos | `Compila/Definiciones.lean`, `Compila/Etapa1.lean`, `Compila/Etapa2.lean`, `Compila/Etapa3.lean` |
| Resultado de `lake build` | **Build completed successfully** (0 errores, solo avisos `declaration uses sorry`) |

Cómo reproducir:

```
lake build            # compila los cuatro archivos
```

### Nota sobre la instalación en esta sesión

El proxy de la sesión bloquea `release.lean-lang.org`, `reservoir.lean-lang.org`,
`cache.mathlib.org` y `lakecache.blob.core.windows.net`. Consecuencias:

- El toolchain se bajó de GitHub Releases y se registró con `elan toolchain link`.
- Mathlib se declara en `lakefile.toml` por URL git, no por Reservoir.
- `lake exe cache get` no funciona, así que Mathlib se compiló desde fuente.
  Por eso los archivos importan módulos concretos (`import Mathlib.LinearAlgebra.UnitaryGroup`,
  etc.) en vez de `import Mathlib`. En una máquina normal, `lake exe cache get` seguido de
  `lake build` funciona igual, y se puede sustituir la lista de imports por `import Mathlib`.
- `import Mathlib` completo: ver la sección "Verificación de `import Mathlib`" al final.

## Tabla: definiciones y enunciados

Leyenda de la columna "Origen": **Mathlib** = se usa el objeto de Mathlib con ese nombre;
**Propio** = definición mínima nuestra; **Mathlib+Propio** = definición propia construida
con piezas de Mathlib.

### `Definiciones.lean`

| Nombre | Qué es | Estado | Origen |
|---|---|---|---|
| `SU2` | grupo especial unitario 2×2 sobre ℂ, como tipo | COMPILA | Mathlib: `Matrix.specialUnitaryGroup (Fin 2) ℂ` |
| instancia `Group SU2` | estructura de grupo | COMPILA | Mathlib (instancia de `specialUnitaryGroup`) |
| instancia `TopologicalSpace SU2` | topología de subtipo de `Matrix (Fin 2) (Fin 2) ℂ` | COMPILA | Mathlib (`Mathlib.Topology.Instances.Matrix` + `Complex.instNormedField`) |
| `LieRing (Matrix (Fin 2) (Fin 2) ℂ)` | corchete = conmutador | COMPILA | Mathlib: `LieRing.ofAssociativeRing`, activada como instancia local (igual que hace Mathlib) |
| `LieAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ)` | álgebra de Lie real | COMPILA | Mathlib: `LieAlgebra.ofAssociativeAlgebra` + `Complex.instAlgebraOfReal` |
| `su2` | matrices antihermitianas de traza cero, como `LieSubalgebra ℝ` | COMPILA (4 obligaciones de cierre con `sorry`) | Mathlib+Propio (`LieSubalgebra`, `conjTranspose`, `trace`) |
| `Ad g X = g * X * g⁻¹` | acción adjunta SU2 × su2 → su2 | COMPILA (pertenencia a `su2` con `sorry`) | Propio |
| `frobNormSq X = Re tr(X Xᴴ)` | cuadrado de la norma de Frobenius | COMPILA | Mathlib+Propio (`Matrix.trace`, `Complex.re`) |
| `unitSphere_su2` | `{X ∈ su2 : frobNormSq X = 1}` | COMPILA | Propio (norma elegida: **Frobenius**) |
| `P` | tipo con un solo elemento | COMPILA | Mathlib: `Unit` |
| `EsSingleton α` | "α tiene exactamente un elemento" | COMPILA | Mathlib: `Nonempty (Unique α)` |

### `Etapa1.lean` (propiedades de SU(2))

| Nombre | Enunciado | Estado | Origen |
|---|---|---|---|
| `C1_isotropia` | `∀ X ∈ unitSphere_su2, ∀ Y ∈ unitSphere_su2, ∃ g : SU2, Ad g X = Y` | COMPILA (sorry) | Propio |
| `C2_indivisibilidad` | `LieAlgebra.IsSimple ℝ su2` | COMPILA (sorry) | Mathlib: `LieAlgebra.IsSimple` (el nombre pedido `IsSimpleLieAlgebra` no existe) |
| `C3_homogeneidad` | `∀ g h : SU2, ∃ k : SU2, k * g = h` | COMPILA, **PROBADO** | Mathlib (`Group`) |
| `C4_compacto` | `CompactSpace SU2` | COMPILA (sorry) | Mathlib: `CompactSpace` |
| `C4_cerrado` | `∀ g h : SU2, g * h ∈ Set.univ` | COMPILA, **PROBADO** | Mathlib |
| `DR_singleton` | `EsSingleton P` (= `Nonempty (Unique P)`) | COMPILA, **PROBADO** | Mathlib: `Unique` (adaptado, ver abajo) |
| `DR_infinito` | `Infinite SU2` | COMPILA (sorry) | Mathlib: `Infinite` |
| `gPolar` | testigo `diag(i, −i) ∈ SU2` | COMPILA, **PROBADO** (pertenencia demostrada) | Mathlib+Propio |
| `polaridad` | `∃ g : SU2, g ≠ g⁻¹` | COMPILA, **PROBADO** | Mathlib |
| `continuo_conexo` | `ConnectedSpace SU2` | COMPILA (sorry) | Mathlib: `ConnectedSpace` |
| `bonus_S3` | `Nonempty (SU2 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)` | COMPILA (sorry) | Mathlib: `Homeomorph`, `Metric.sphere`, `EuclideanSpace` |

Adaptación en `DR_singleton`: el guion pedía `theorem DR_singleton : Unique P`. `Unique P` es un
`Type`, no una `Prop`, y Lean 4 rechaza un `theorem` cuyo tipo no sea una proposición. Se
enuncia como `Nonempty (Unique P)`, que es equivalente y sí es `Prop`.

### `Etapa2.lean` (unicidad)

| Nombre | Qué es | Estado | Origen |
|---|---|---|---|
| `LieGroupCompactoConexo G` | clase: `Group`, `TopologicalSpace`, `IsTopologicalGroup`, `T2Space` (Hausdorff), `CompactSpace`, `ConnectedSpace`, más un álgebra de Lie real `𝔤`, `Ad : G →* (𝔤 ≃ₗ[ℝ] 𝔤)` **fiel** (`Ad_injective`) y una forma cuadrática `normSq` `Ad`-invariante | COMPILA | Propio (construida con clases de Mathlib) |
| `lieAlgebra G` | el campo `𝔤` de la clase | COMPILA | Propio |
| `esfera G` | `{X : lieAlgebra G | normSq X = 1}` | COMPILA | Propio |
| `AlgebraSimple L` | `LieAlgebra.IsSimple ℝ L` | COMPILA | Mathlib (alias) |
| `AdTransitivaEnEsfera G` | `∀ X ∈ esfera G, ∀ Y ∈ esfera G, ∃ g, Ad g X = Y` | COMPILA | Propio |
| `EsFormaFundamental G` | `AlgebraSimple (lieAlgebra G) ∧ AdTransitivaEnEsfera G` | COMPILA | Propio |
| `SO3` | grupo especial ortogonal 3×3 sobre ℝ, como tipo | COMPILA (`Group SO3` se infiere) | Mathlib: `Matrix.specialOrthogonalGroup (Fin 3) ℝ` |
| `unicidad` | `EsFormaFundamental G → Nonempty (G ≃* SU2) ∨ Nonempty (G ≃* SO3)` | COMPILA (sorry) | Mathlib: `MulEquiv` |

### `Etapa3.lean` (convergencia)

| Nombre | Qué es | Estado | Origen |
|---|---|---|---|
| `CurvaturaPositivaConstante G` | curvatura seccional positiva constante | COMPILA (declarado `opaque`, **NO FORMALIZADO**; **ya no se usa en A3**, se conserva como referencia) | Propio, opaco |
| `A1_clausura G` | `CompactSpace G` | COMPILA | Mathlib |
| `A2_convergencia P G` | `EsSingleton P ∧ Infinite G ∧ AlgebraSimple (lieAlgebra G)` | COMPILA | Mathlib+Propio |
| `A3_relieve G` | `(⊤ : LieSubalgebra ℝ (lieAlgebra G)) ≠ ⊥ ∧ (∃ g h, g ≠ 1 ∧ h ≠ 1 ∧ ¬ IsConj g h)` (sin curvatura) | COMPILA | Mathlib (`LieSubalgebra`, `IsConj`) |
| `A4_isotropia G` | `AdTransitivaEnEsfera G` | COMPILA | Propio |
| `C1 G` … `C5 G` | versiones genéricas de C1, C2, C3, C4 (compacto ∧ cerrado), C5 = polaridad | COMPILAN | Mathlib+Propio |
| `DR P G` | `EsSingleton P ∧ Infinite G` | COMPILA | Mathlib |
| `Continuo G` | `ConnectedSpace G` | COMPILA | Mathlib |
| `A1_clausura_holds`, `C3_holds`, `C4_holds`, `Continuo_holds` | A1, C3, C4 y Continuo se cumplen para todo `G` de la clase | COMPILAN, **PROBADO** | — |
| `convergencia` | `(A1 ∧ A2 ∧ A3 ∧ A4) ↔ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ DR ∧ Continuo)` | COMPILA (sorry) | — |
| `corolario` | `(A1 ∧ A2 ∧ A3 ∧ A4) → Nonempty (G ≃* SU2) ∨ Nonempty (G ≃* SO3)` | COMPILA (sorry) | Mathlib: `MulEquiv` |

Nota sobre `lieAlgebra G ≠ ⊥`: un tipo no se compara con `⊥`; se escribe como
`⊤ ≠ ⊥` en el retículo de subálgebras de Lie de `lieAlgebra G`, que es la lectura literal
"el álgebra de Lie no es el álgebra cero".

## Nociones que NO están en Mathlib y hubo que definir

1. **`su(2)` con nombre.** Mathlib tiene `Matrix.specialUnitaryGroup` pero no su álgebra de
   Lie. `su2` se define como `LieSubalgebra ℝ` de las matrices complejas 2×2 con las
   condiciones `Xᴴ = -X` y `trace X = 0`.
2. **Acción adjunta de un grupo matricial sobre su álgebra de Lie (`Ad`).** Mathlib solo tiene
   `LieAlgebra.ad` (la acción del álgebra sobre sí misma).
3. **Norma de Frobenius como instancia global.** Mathlib la tiene
   (`Matrix.frobeniusNormedAddCommGroup`) pero solo como instancia local; se define
   `frobNormSq` a mano.
4. **La esfera unidad de `su2`** (`unitSphere_su2`).
5. **`LieGroupCompactoConexo`.** Mathlib tiene `LieGroup I n G` (sobre variedades con
   `ChartedSpace`), pero no construye el álgebra de Lie de un `LieGroup`, ni `Ad`, ni métricas
   bi-invariantes, y `SU2` no tiene instancia `ChartedSpace`. La clase propia empaqueta solo los
   datos que los enunciados necesitan.
6. **`lieAlgebra G`, `esfera G`, `AdTransitivaEnEsfera G`, `EsFormaFundamental G`** sobre la
   clase anterior.
7. **`CurvaturaPositivaConstante G`.** Mathlib v4.34.0 no tiene curvatura seccional, conexión
   de Levi-Civita ni métrica bi-invariante. Se deja como `opaque` (proposición con nombre y sin
   contenido). **Se ha retirado de `A3_relieve`** porque, al ser opaca, hacía indemostrable la
   dirección ← de `convergencia` (ver `ANALISIS_convergencia.md`); la declaración se conserva
   solo como referencia.
8. **Los predicados A1–A4, C1–C5, DR, Continuo** son definiciones propias a partir de piezas de
   Mathlib.

Nombres del guion que se adaptaron a los reales de Mathlib:

| Pedido | Real en Mathlib |
|---|---|
| `IsSimpleLieAlgebra su2` | `LieAlgebra.IsSimple ℝ su2` |
| `SO3` | `Matrix.specialOrthogonalGroup (Fin 3) ℝ` |
| `Singleton P` / `Unique P` como teorema | `Nonempty (Unique P)` (`Unique` es un `Type`) |
| `lieAlgebra G ≠ ⊥` | `(⊤ : LieSubalgebra ℝ (lieAlgebra G)) ≠ ⊥` |

## Resumen

1. **Enunciados**: 44 declaraciones (17 teoremas: 10 en Etapa1, 1 en Etapa2, 6 en Etapa3; y
   27 definiciones, clases y predicados) y todas COMPILAN; 0 NO COMPILAN. De los 17 teoremas,
   8 están **PROBADOS** (los cuatro triviales de Etapa1: C3, C4_cerrado, DR_singleton,
   polaridad; y sus cuatro versiones genéricas en Etapa3: A1_clausura_holds, C3_holds,
   C4_holds, Continuo_holds) y 9 quedan con `sorry`.
2. **Definiciones propias**: 8 grupos de nociones no están en Mathlib (lista anterior); la única
   sin contenido matemático es `CurvaturaPositivaConstante`, que queda opaca.
3. **Planteamiento**: el problema está bien planteado en el lenguaje formal, con una
   salvedad: `LieGroupCompactoConexo` es una clase propia (grupo topológico Hausdorff compacto
   conexo con un álgebra de Lie real y `Ad` fiel), de modo que `unicidad`, `convergencia` y
   `corolario` son enunciados sobre esa clase, no sobre el `LieGroup` de Mathlib. La curvatura
   se ha retirado de las hipótesis porque no era formalizable. Todo lo demás (SU2, su2, Ad,
   esfera, simplicidad, compacidad, conexión, S³, SO3, isomorfismos de grupos) usa nociones
   estándar de Mathlib y tipa correctamente. El análisis de qué partes de `convergencia` son
   desempaquetado y cuáles tienen contenido está en `ANALISIS_convergencia.md`.

## Verificación de `import Mathlib`

PENDIENTE: se está compilando Mathlib completo desde fuente en segundo plano (6.122 módulos).
Este apartado se actualiza al terminar.
