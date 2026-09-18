# ETAPA 3 — CONVERGENCIA DE LAS CUATRO EXIGENCIAS (`Compila/Etapa3.lean`)

Todas las definiciones son predicados sobre `S : LieStructure` (etapa 2): `S.P`, `S.G`
(grupo de Lie, `LieGroup (𝓡 n) ∞ S.G`), `S.𝔤` (álgebra de Lie con producto interior
invariante), `S.Ad`.

## Definiciones exactas elegidas

| Predicado | Definición Lean |
|---|---|
| **A1 Clausura** | `CompactSpace S.G ∧ ∀ g h : S.G, ∃ k, g * h = k` |
| **A2 Convergencia sin partir** | `(Subsingleton S.P ∧ Nonempty S.P) ∧ Infinite S.G ∧ (∀ g (p : S.P), g • p = p) ∧ LieAlgebra.IsSimple ℝ S.𝔤` |
| **A3 Relieve** | `Nontrivial S.𝔤 ∧ (∃ g h : S.G, g ≠ 1 ∧ h ≠ 1 ∧ ¬ IsConj g h) ∧ S.ConstantPositiveCurvature` |
| `ConstantPositiveCurvature` | `∃ κ > 0, ∀ x y : S.𝔤, ‖⁅x, y⁆‖² = 4κ (‖x‖²‖y‖² − ⟪x, y⟫²)` |
| **A4 Isotropía** | `AdTransitive S` = `∀ v w : S.𝔤, ‖v‖ = 1 → ‖w‖ = 1 → ∃ g, S.Ad g v = w` |
| **C1** | `AdTransitive S` |
| **C2** | `LieAlgebra.IsSimple ℝ S.𝔤` |
| **C3** | `MulAction.IsPretransitive S.G S.G` |
| **C4** | `CompactSpace S.G ∧ ∀ g h, ∃ k, g * h = k` |
| **C5** | `∀ r : S.G → S.G → Prop, ¬ IsInvariantTotalOrder r` (ningún orden total estricto invariante por la operación) |
| **DR** | `(Subsingleton S.P ∧ Nonempty S.P) ∧ Infinite S.G` |
| **Continuo** | `ConnectedSpace S.G` (la estructura de variedad `C^∞` es un dato de `LieStructure`) |

**Sobre la curvatura.** Mathlib no define la curvatura seccional. Para una métrica
bi-invariante en un grupo de Lie la fórmula clásica es
`K(x, y) = ¼ ‖⁅x, y⁆‖² / (‖x‖²‖y‖² − ⟪x, y⟫²)`; «curvatura seccional constante `κ > 0`»
se formaliza como la identidad polinómica anterior para todo `x, y ∈ 𝔤`. Es una
definición honesta pero a nivel del álgebra de Lie, no de la geometría riemanniana de
Mathlib (`Geometry.Manifold.Riemannian` sólo contiene métricas, no curvatura).

**Sobre «elementos de distinta magnitud».** Se formaliza como la existencia de dos
elementos no triviales **no conjugados** (`¬ IsConj g h`): hay más de una «clase de
magnitud» de lecturas.

## Teorema de convergencia

`convergencia (S) [ConnectedSpace S.G] : (S.A1 ∧ S.A2 ∧ S.A3 ∧ S.A4) ↔
(S.C1 ∧ S.C2 ∧ S.C3 ∧ S.C4 ∧ S.C5 ∧ S.DR ∧ S.Continuo)`

| Dirección | Estado | Contenido |
|---|---|---|
| **(→)** `convergencia_mp` | **PROBADO módulo los 3 axiomas de la etapa 2** | `C1 = A4`, `C2 ⊂ A2`, `C3` siempre cierto, `C4 = A1`, `DR ⊂ A2`, `Continuo` = hipótesis: **desempaquetado**. `C5` tiene contenido real: por la clasificación, `G ≅ SU(2)` o `SO(3)`, que contienen una involución no trivial (`−1`, resp. `diag(1,−1,−1)`), luego `G` no admite órdenes totales invariantes (`involution_and_nonconj`, `no_invariant_order_of_involution`). |
| **(←)** `convergencia_mpr` | **PROBADO módulo los 3 axiomas de la etapa 2** | `A1 = C4`, `A4 = C1`, `A2` = `DR` + acción trivial (de `Subsingleton P`) + `C2`: **desempaquetado**. `A3` tiene contenido real: (i) `𝔤 ≠ 0` por simplicidad; (ii) elementos no conjugados por la clasificación (`−1` y `i` en `S³`, `−1` es central; en `SO(3)`, dos rotaciones de trazas distintas, `trace_eq_of_isConj_SO3`); (iii) **curvatura constante positiva**: de `dim 𝔤 = 3` (etapa 2) y el paso 2 de la etapa 2, `⁅x, y⁆ = c·(x × y)` en coordenadas ortonormales, y la identidad de Lagrange da `‖⁅x, y⁆‖² = c²(‖x‖²‖y‖² − ⟪x, y⟫²)`, i.e. `κ = c²/4` (`constant_curvature`, **probado sin axiomas**). |

La parte con **contenido real** es, como se anticipaba, `A3`: la curvatura constante y la
no conjugación no son desempaquetado, y se obtienen de la clasificación. `C5` también
usa la clasificación. Ninguna de las dos direcciones tiene `sorry`; ambas dependen
exactamente de `montgomery_samelson_borel`, `adImageDim`, `adImageDim_eq_of_isSimple`
y `lie_group_of_su2` (`#print axioms`).

## Corolario

`corolario (S) [ConnectedSpace S.G] (h : S.A1 ∧ S.A2 ∧ S.A3 ∧ S.A4) :
Nonempty (S.𝔤 ≃ₗ⁅ℝ⁆ su2Model) ∧ (Nonempty (S.G ≃ₜ* SU2) ∨ Nonempty (S.G ≃ₜ* SO3))`

**PROBADO módulo los 3 axiomas de la etapa 2** (sin `sorry`): `A1` da compacidad, `A2`
simplicidad, `A4` transitividad, y se aplica `clasificacion`.

## Existencia dentro del marco

`S3Structure : LieStructure` es la estructura `({∗}, S³ ≅ SU(2))` del tratado, con
`𝔤 = ImH`, `Ad = AdS3`. Se prueba `S3Structure_A : A1 ∧ A2 ∧ A3 ∧ A4` **sin usar ningún
axioma ni `sorry`** (la curvatura constante se obtiene directamente de `dim ImH = 3` y de
la invariancia del producto interior; los elementos no conjugados son `−1` e `i`).
