# ETAPA 2 — UNICIDAD EN LA CLASE (`Compila/Etapa2.lean`)

**Teorema.** Todo grupo de Lie compacto y conexo cuya álgebra de Lie es simple y cuya
acción adjunta actúa transitivamente sobre la esfera unidad de su álgebra de Lie tiene
álgebra de Lie de dimensión 3 y es isomorfo a `SU(2)` o a `SO(3)`.

Enunciado Lean: `clasificacion (S : LieStructure) [CompactSpace S.G] [ConnectedSpace S.G]
[LieAlgebra.IsSimple ℝ S.𝔤] (htrans : AdTransitive S) :
Module.finrank ℝ S.𝔤 = 3 ∧ Nonempty (S.𝔤 ≃ₗ⁅ℝ⁆ su2Model) ∧
(Nonempty (S.G ≃ₜ* SU2) ∨ Nonempty (S.G ≃ₜ* SO3))`.

## Marco

Mathlib v4.34 no dispone de la teoría de Lie de grupos compactos (acción adjunta de un
grupo de Lie, dimensión de subgrupos cerrados, teoremas de Lie). Se introduce la interfaz
`LieStructure`, que empaqueta como **datos**: un grupo topológico `G` con instancia
`LieGroup` de Mathlib; un álgebra de Lie real `𝔤` de dimensión finita con producto
interior **invariante** (`⟪⁅x,y⁆, z⟫ = ⟪x, ⁅y,z⁆⟫`, que existe siempre para `G`
compacto promediando con Haar); un homomorfismo `Ad : G →* O(𝔤)` que respeta el corchete;
y un conjunto `P` sobre el que actúa `G`. **No** se prueba que `𝔤` coincide con el
espacio tangente de Mathlib (`GroupLieAlgebra`), cuyo corchete apenas está desarrollado.

`𝔰𝔲(2)` canónica: `su2Model := (ℝ³, ×)` (producto vectorial), con `su2Model.isSimple`
**probado**.

## Estado de cada paso

| Paso | Estado | Declaración | Comentario |
|---|---|---|---|
| Tabla de Montgomery–Samelson–Borel: si `H ⊆ SO(n)` compacto conexo actúa transitivamente sobre `S^{n−1}`, `(n, dim H)` ∈ {`SO(n)`, `U(m)`, `SU(m)`, `Sp(m)`, `Sp(m)·U(1)`, `Sp(m)·Sp(1)`, `G₂`, `Spin(7)`, `Spin(9)`}, con indicador de simplicidad de `Lie(H)` | **AXIOMA** | `montgomery_samelson_borel`, `MSBTable` | No está en Mathlib (ni la noción de «subgrupo cerrado de `SO(n)` con su dimensión»). Se admite con nombre, aplicado a `H = Ad(G)`. |
| Dimensión de `Ad(G)`: noción primitiva `adImageDim` | **AXIOMA** (noción primitiva) | `adImageDim` | Mathlib no define la dimensión de un subgrupo cerrado de `GL(𝔤)`. |
| `dim Ad(G) = dim 𝔤` si `𝔤` es simple (`ker ad = Z(𝔤) = 0`, `Ad(G) ≅ G/Z(G)`) | **AXIOMA** | `adImageDim_eq_of_isSimple` | Teoría de Lie no disponible en Mathlib. |
| Aritmética: `dim H = n` y `Lie(H)` simple fuerzan `n = 3` (resuelve `2n = n(n−1)`, `2m+1 = m²`, `4m = m(2m+1)`, `4m = 2m²+m+1` ⇒ `U(2)` excluido por no simple, etc.) | **PROBADO** | `msb_arith` | Sin axiomas. |
| `𝔤` simple ⇒ `dim 𝔤 ≠ 0` | **PROBADO** | `finrank_ne_zero_of_isSimple` | |
| **Paso 1:** `dim 𝔤 = 3` | **PROBADO módulo axiomas 1–2** | `finrank_eq_three` | `#print axioms`: `adImageDim`, `adImageDim_eq_of_isSimple`, `montgomery_samelson_borel`. |
| **Paso 2:** álgebra de Lie real de dimensión 3, no abeliana, con producto interior invariante ⇒ `≅ (ℝ³, ×) = 𝔰𝔲(2)` | **PROBADO** (sin axiomas) | `exists_lieEquiv_su2Model`, `coords_bracket`, `strC_table` | La forma `ω(x,y,z) = ⟪⁅x,y⁆, z⟫` es alternada por invariancia; en base ortonormal `⁅x, y⁆ = c·(x × y)` con `c = ⟪e₂, ⁅e₀,e₁⁆⟫`; no abeliana ⇒ `c ≠ 0`; `x ↦ c·coords(x)` es un isomorfismo de álgebras de Lie. Aquí la invariancia del producto interior hace el papel de la compacidad (excluye `𝔰𝔩(2,ℝ)`). |
| **Paso 3:** grupo de Lie compacto conexo con álgebra `𝔰𝔲(2)` es `SU(2)` o `SU(2)/{±1} = SO(3)` | **AXIOMA** | `lie_group_of_su2` | Teoremas de Lie + recubridor universal `S³` + `Z(SU(2)) = {±1}`; no disponible en Mathlib. |
| **Teorema de clasificación** | **PROBADO módulo los 3 axiomas** | `clasificacion` | `#print axioms`: los tres axiomas nombrados (más los estándar). Sin `sorry`. |

No hay ningún `sorry` en la etapa 2. Los axiomas están aislados y nombrados; el
resto (aritmética diofántica y el álgebra lineal del paso 2) está verificado por Lean.
