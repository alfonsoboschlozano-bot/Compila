/-
# ETAPA 2 — UNICIDAD EN LA CLASE

**Teorema (clasificación).** Todo grupo de Lie compacto y conexo cuya álgebra de Lie es
simple y cuya acción adjunta actúa transitivamente sobre la esfera unidad de su álgebra
de Lie tiene álgebra de Lie de dimensión 3 y es isomorfo a `SU(2)` o a `SO(3)`.

## Marco abstracto

Mathlib (v4.34) **no** dispone de la teoría de Lie de grupos compactos: no define la
acción adjunta de un grupo de Lie, ni la dimensión de un subgrupo cerrado, ni la
correspondencia grupo ↔ álgebra (teoremas de Lie). Por ello introducimos una interfaz
abstracta `LieStructure` que empaqueta, como *datos*, exactamente lo que el teorema usa:

* un grupo topológico `G` con estructura de grupo de Lie (`LieGroup` de Mathlib);
* un álgebra de Lie real `𝔤` de dimensión finita con un producto interior
  **invariante** (`⟪⁅x,y⁆, z⟫ = ⟪x, ⁅y,z⁆⟫`; existe siempre para `G` compacto,
  promediando con la medida de Haar);
* un homomorfismo `Ad : G →* O(𝔤)` (isometrías lineales) que respeta el corchete.

`𝔤` se toma como dato; **no** probamos que coincide con el espacio tangente en la
identidad (`GroupLieAlgebra` de Mathlib), cuyo corchete apenas está desarrollado.

## Axiomas admitidos (con nombre)

1. `montgomery_samelson_borel` — la clasificación de Montgomery–Samelson–Borel (1940-43)
   de los grupos compactos conexos que actúan transitivamente sobre esferas, en la forma
   «tabla de dimensiones»: si `H ⊆ SO(n)` es compacto, conexo y transitivo sobre
   `S^{n-1}`, entonces `(n, dim H)` está en una lista finita de familias.
2. `adImageDim_eq_of_isSimple` — `Ad(G) ≅ G / Z(G)` tiene la misma dimensión que `𝔤`
   cuando `𝔤` es simple (el núcleo de `ad` es el centro de `𝔤`, que es nulo).
3. `lie_group_of_su2` — un grupo de Lie compacto conexo con álgebra de Lie `𝔰𝔲(2)` es
   `SU(2)` o `SU(2)/{±1} = SO(3)` (teoremas de Lie + `Z(SU(2)) = {±1}`).

Todo lo demás (la aritmética que fuerza `n = 3`, y que una álgebra de Lie real de
dimensión 3 no abeliana con producto interior invariante es `𝔰𝔲(2) ≅ (ℝ³, ×)`)
**se prueba**.
-/
import Compila.Etapa1

open Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Compila

/-! ## El modelo canónico de `𝔰𝔲(2)`: `ℝ³` con el producto vectorial -/

/-- `ℝ³` con el corchete `⁅u, v⁆ = u ×₃ v`. Sinónimo de tipo para evitar el conflicto de
instancias con `LieRing.ofAssociativeRing`. -/
def su2Model : Type := Fin 3 → ℝ

namespace su2Model

instance : AddCommGroup su2Model := Pi.addCommGroup
instance : Module ℝ su2Model := Pi.module _ _ _
instance : LieRing su2Model := Cross.lieRing
instance : LieAlgebra ℝ su2Model where
  lie_smul t x y := LinearMap.map_smul (crossProduct (x : Fin 3 → ℝ)) t y

/-- Vista de un elemento de `su2Model` como vector de `ℝ³`. -/
def vec (x : su2Model) : Fin 3 → ℝ := x

/-- Un vector de `ℝ³` como elemento de `su2Model`. -/
def ofVec (v : Fin 3 → ℝ) : su2Model := v

theorem vec_injective : Function.Injective vec := fun _ _ h => h

@[simp] theorem vec_ofVec (v : Fin 3 → ℝ) : vec (ofVec v) = v := rfl
@[simp] theorem vec_add (x y : su2Model) : vec (x + y) = vec x + vec y := rfl
@[simp] theorem vec_sub (x y : su2Model) : vec (x - y) = vec x - vec y := rfl
@[simp] theorem vec_smul (t : ℝ) (x : su2Model) : vec (t • x) = t • vec x := rfl
@[simp] theorem vec_zero : vec (0 : su2Model) = 0 := rfl

/-- El corchete es el producto vectorial. -/
theorem vec_bracket (x y : su2Model) : vec ⁅x, y⁆ = crossProduct (vec x) (vec y) := rfl

/-- `(ℝ³, ×)` es simple. -/
theorem isSimple : LieAlgebra.IsSimple ℝ su2Model where
  eq_bot_or_eq_top := by
    intro I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      obtain ⟨v, hvI, hv0⟩ : ∃ v ∈ I, v ≠ 0 := by
        by_contra hcon
        exact hI ((LieSubmodule.eq_bot_iff I).mpr fun m hm =>
          by_contra fun h0 => hcon ⟨m, hm, h0⟩)
      rw [eq_top_iff]
      intro u _
      have key : ⁅v, ⁅u, v⁆⁆ = (dotProduct (vec v) (vec v)) • u - (dotProduct (vec v) (vec u)) • v := by
        apply vec_injective
        rw [vec_bracket, vec_bracket, vec_sub, vec_smul, vec_smul,
          cross_cross_eq_smul_sub_smul', dotProduct_comm (vec u) (vec v)]
      have key' : (dotProduct (vec v) (vec v)) • u = ⁅v, ⁅u, v⁆⁆ + (dotProduct (vec v) (vec u)) • v := by
        rw [key]; abel
      have hmem : (dotProduct (vec v) (vec v)) • u ∈ I := by
        rw [key']
        exact I.add_mem (I.lie_mem (I.lie_mem hvI)) (I.smul_mem _ hvI)
      have hne : dotProduct (vec v) (vec v) ≠ 0 := fun h =>
        hv0 (vec_injective (by rw [vec_zero]; exact dotProduct_self_eq_zero.mp h))
      have := I.smul_mem (dotProduct (vec v) (vec v))⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  non_abelian := by
    intro h
    have h0 := h.trivial (ofVec ![1, 0, 0]) (ofVec ![0, 1, 0])
    have := congrFun (congrArg vec h0) 2
    rw [vec_bracket, vec_ofVec, vec_ofVec, vec_zero] at this
    simp [cross_apply] at this

end su2Model

/-! ## La interfaz abstracta: grupo de Lie compacto con álgebra de Lie y acción adjunta -/

/-- Estructura `F = (P, G)`: un punto-conjunto `P` sobre el que actúa un grupo de Lie `G`,
junto con su álgebra de Lie `𝔤` (con producto interior invariante) y la acción adjunta. -/
structure LieStructure where
  /-- El «punto» (o conjunto de puntos) leído por `G`. -/
  P : Type
  /-- El grupo de lecturas. -/
  G : Type
  [instGroup : Group G]
  [instTop : TopologicalSpace G]
  [instTopGroup : IsTopologicalGroup G]
  [instT2 : T2Space G]
  /-- Dimensión de `G` como variedad. -/
  n : ℕ
  [instCharted : ChartedSpace (EuclideanSpace ℝ (Fin n)) G]
  /-- `G` es un grupo de Lie `C^∞`. -/
  [instLieGroup : LieGroup (𝓡 n) ∞ G]
  /-- El álgebra de Lie de `G`. -/
  𝔤 : Type
  [instNormed : NormedAddCommGroup 𝔤]
  [instInner : InnerProductSpace ℝ 𝔤]
  [instFinite : FiniteDimensional ℝ 𝔤]
  [instBracket : LieBracketOn 𝔤]
  [instBracketSMul : LieBracketSMul ℝ 𝔤]
  finrank_eq : Module.finrank ℝ 𝔤 = n
  /-- La acción adjunta, por isometrías lineales de `𝔤`. -/
  Ad : G →* (𝔤 ≃ₗᵢ[ℝ] 𝔤)
  Ad_bracket : ∀ (g : G) (x y : 𝔤), Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆
  /-- Invariancia del producto interior (métrica bi-invariante). -/
  inner_bracket : ∀ x y z : 𝔤, (inner ℝ ⁅x, y⁆ z : ℝ) = inner ℝ x ⁅y, z⁆
  [instAction : MulAction G P]

attribute [instance] LieStructure.instGroup LieStructure.instTop LieStructure.instTopGroup
  LieStructure.instT2 LieStructure.instCharted LieStructure.instLieGroup
  LieStructure.instNormed LieStructure.instInner LieStructure.instFinite
  LieStructure.instBracket LieStructure.instBracketSMul LieStructure.instAction

/-- La acción adjunta es transitiva sobre la esfera unidad de `𝔤`. -/
def AdTransitive (S : LieStructure) : Prop :=
  ∀ v w : S.𝔤, ‖v‖ = 1 → ‖w‖ = 1 → ∃ g : S.G, S.Ad g v = w

/-- `SO(3)` como grupo de matrices reales 3×3 ortogonales de determinante 1. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-! ## Axioma 1: Montgomery–Samelson–Borel (forma «tabla de dimensiones») -/

/-- Tabla de Montgomery–Samelson–Borel. Si un grupo compacto conexo `H ⊆ SO(n)` actúa
transitivamente sobre `S^{n-1}`, entonces `H` es (conjugado a) uno de:
`SO(n)`, `U(m)`, `SU(m)` (`n = 2m`), `Sp(m)`, `Sp(m)·U(1)`, `Sp(m)·Sp(1)` (`n = 4m`),
`G₂` (`n = 7`), `Spin(7)` (`n = 8`), `Spin(9)` (`n = 16`).
Registramos `(n, d = dim H)` y, para las familias cuya álgebra de Lie tiene centro no
trivial o no es simple, el hecho `¬ simple`. -/
def MSBTable (n d : ℕ) (simple : Prop) : Prop :=
  (2 * d = n * (n - 1)) ∨                                   -- SO(n)
  (∃ m, n = 2 * m ∧ d = m ^ 2 ∧ ¬ simple) ∨                 -- U(m)   (𝔲(m) tiene centro)
  (∃ m, n = 2 * m ∧ d + 1 = m ^ 2) ∨                        -- SU(m)
  (∃ m, n = 4 * m ∧ d = m * (2 * m + 1)) ∨                  -- Sp(m)
  (∃ m, n = 4 * m ∧ d = 2 * m ^ 2 + m + 1 ∧ ¬ simple) ∨     -- Sp(m)·U(1)
  (∃ m, n = 4 * m ∧ d = 2 * m ^ 2 + m + 3 ∧ ¬ simple) ∨     -- Sp(m)·Sp(1)
  (n = 7 ∧ d = 14) ∨ (n = 8 ∧ d = 21) ∨ (n = 16 ∧ d = 36)   -- G₂, Spin(7), Spin(9)

/-- **AXIOMA (dimensión de `Ad(G)`).** Mathlib no define la dimensión de un subgrupo
cerrado de `GL(𝔤)`; la introducimos como noción primitiva. -/
axiom adImageDim (S : LieStructure) : ℕ

/-- **AXIOMA 2.** Si `𝔤` es simple, su centro es nulo, luego `ad : 𝔤 → 𝔤𝔩(𝔤)` es inyectiva
y `Ad(G) ≅ G/Z(G)` tiene álgebra de Lie `ad(𝔤) ≅ 𝔤`; en particular `dim Ad(G) = dim 𝔤`. -/
axiom adImageDim_eq_of_isSimple (S : LieStructure) [LieAlgebra.IsSimple ℝ S.𝔤] :
    adImageDim S = Module.finrank ℝ S.𝔤

/-- **AXIOMA 1 (Montgomery–Samelson–Borel).** `Ad(G)` es un subgrupo compacto conexo de
`O(𝔤) ≅ O(n)` (imagen continua de un compacto conexo); si actúa transitivamente sobre la
esfera unidad `S^{n-1} ⊂ 𝔤`, entonces `(n, dim Ad(G))` está en la tabla, con el
indicador de simplicidad referido a `Lie(Ad G) ≅ 𝔤` (véase el axioma 2). -/
axiom montgomery_samelson_borel (S : LieStructure) [CompactSpace S.G] [ConnectedSpace S.G]
    (htrans : AdTransitive S) :
    MSBTable (Module.finrank ℝ S.𝔤) (adImageDim S) (LieAlgebra.IsSimple ℝ S.𝔤)

/-! ## Paso aritmético (probado): `dim H = n` y `Lie(H)` simple fuerzan `n = 3` -/

theorem msb_arith (n : ℕ) (hn : n ≠ 0) (simple : Prop) (hs : simple)
    (h : MSBTable n n simple) : n = 3 := by
  rcases h with h | ⟨m, h1, h2, h3⟩ | ⟨m, h1, h2⟩ | ⟨m, h1, h2⟩ | ⟨m, h1, h2, h3⟩ |
    ⟨m, h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- SO(n): 2n = n(n-1) ⇒ n = 3
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h
    have : 2 = k := by nlinarith
    omega
  · exact absurd hs h3
  · -- SU(m): 2m + 1 = m² no tiene solución
    subst h1
    exfalso
    rcases Nat.lt_or_ge m 3 with hm | hm
    · nlinarith [sq m]
    · nlinarith [sq m]
  · -- Sp(m): 4m = m(2m+1) ⇒ m = 0 (excluido)
    subst h1
    exfalso
    have hm : m ≠ 0 := by omega
    have : 4 = 2 * m + 1 := by
      have := Nat.pos_of_ne_zero hm
      nlinarith
    omega
  · exact absurd hs h3
  · exact absurd hs h3
  · omega
  · omega
  · omega

/-- Un álgebra de Lie simple es no trivial (`finrank ≠ 0`). -/
theorem finrank_ne_zero_of_isSimple (𝔤 : Type*) [AddCommGroup 𝔤] [Module ℝ 𝔤]
    [FiniteDimensional ℝ 𝔤] [LieBracketOn 𝔤] [LieBracketSMul ℝ 𝔤]
    [hs : LieAlgebra.IsSimple ℝ 𝔤] : Module.finrank ℝ 𝔤 ≠ 0 := by
  intro h0
  have : Subsingleton 𝔤 := Module.finrank_zero_iff.mp h0
  exact hs.non_abelian ⟨fun x y => Subsingleton.elim _ _⟩

/-- **Paso 1 del teorema (probado módulo axiomas 1–2): `dim 𝔤 = 3`.** -/
theorem finrank_eq_three (S : LieStructure) [CompactSpace S.G] [ConnectedSpace S.G]
    [hs : LieAlgebra.IsSimple ℝ S.𝔤] (htrans : AdTransitive S) :
    Module.finrank ℝ S.𝔤 = 3 := by
  have h := montgomery_samelson_borel S htrans
  rw [adImageDim_eq_of_isSimple S] at h
  exact msb_arith _ (finrank_ne_zero_of_isSimple S.𝔤) _ hs h

/-! ## Paso 2 (probado): álgebra de Lie de dimensión 3, no abeliana, con producto interior
invariante ⇒ `≅ (ℝ³, ×) = 𝔰𝔲(2)`

Idea: la forma trilineal `ω(x, y, z) = ⟪⁅x, y⁆, z⟫` es alternada (por invariancia), luego
en una base ortonormal `e₀, e₁, e₂` vale `ω = c · det`, es decir `⁅x, y⁆ = c · (x × y)`.
Como el álgebra no es abeliana, `c ≠ 0`, y `x ↦ c x` es un isomorfismo con `(ℝ³, ×)`. -/

section ThreeDim

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
  [LieBracketOn 𝔤] [LieBracketSMul ℝ 𝔤]

/-- Base ortonormal de un espacio de dimensión 3, indexada por `Fin 3`. -/
def onb3 (h3 : Module.finrank ℝ 𝔤 = 3) : OrthonormalBasis (Fin 3) ℝ 𝔤 :=
  (stdOrthonormalBasis ℝ 𝔤).reindex (finCongr h3)

variable (hinv : ∀ x y z : 𝔤, (inner ℝ ⁅x, y⁆ z : ℝ) = inner ℝ x ⁅y, z⁆)
  (h3 : Module.finrank ℝ 𝔤 = 3)

/-- Coordenadas de `x` en la base ortonormal, como vector de `ℝ³`. -/
def coords (x : 𝔤) : Fin 3 → ℝ := fun i => inner ℝ (onb3 h3 i) x

theorem sum_coords_smul (x : 𝔤) : ∑ i, coords h3 x i • onb3 h3 i = x :=
  (onb3 h3).sum_repr' x

theorem eq_of_coords_eq {x y : 𝔤} (h : ∀ i, coords h3 x i = coords h3 y i) : x = y := by
  rw [← sum_coords_smul h3 x, ← sum_coords_smul h3 y]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem coords_add (x y : 𝔤) : coords h3 (x + y) = coords h3 x + coords h3 y := by
  funext i; simp [coords, inner_add_right]

theorem coords_smul (t : ℝ) (x : 𝔤) : coords h3 (t • x) = t • coords h3 x := by
  funext i; simp [coords, inner_smul_right]

theorem coords_onb3 (i k : Fin 3) : coords h3 (onb3 h3 i) k = if k = i then 1 else 0 :=
  (orthonormal_iff_ite.mp (onb3 h3).orthonormal) k i

/-- Coeficientes de estructura `strC i j k = ⟪e_k, ⁅e_i, e_j⁆⟫`. -/
def strC (i j k : Fin 3) : ℝ := inner ℝ (onb3 h3 k) ⁅onb3 h3 i, onb3 h3 j⁆

/-- La constante de estructura `c = ⟪e₂, ⁅e₀, e₁⁆⟫`. -/
def structConst : ℝ := strC h3 0 1 2

include hinv in
theorem strC_cyc (i j k : Fin 3) : strC h3 i j k = strC h3 j k i := by
  unfold strC
  rw [real_inner_comm, hinv, real_inner_comm]

theorem strC_same₁ (i k : Fin 3) : strC h3 i i k = 0 := by
  simp [strC]

include hinv in
theorem strC_same₂ (i j : Fin 3) : strC h3 i j j = 0 := by
  rw [strC_cyc hinv, strC_same₁]

theorem strC_swap (i j k : Fin 3) : strC h3 j i k = - strC h3 i j k := by
  unfold strC
  rw [← lie_skew, inner_neg_right]

/-- Símbolo de Levi-Civita. -/
def ε (i j k : Fin 3) : ℝ :=
  if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (2, 0, 1) then 1
  else if (i, j, k) = (1, 0, 2) ∨ (i, j, k) = (2, 1, 0) ∨ (i, j, k) = (0, 2, 1) then -1
  else 0

include hinv in
/-- Tabla completa de los coeficientes de estructura: `strC i j k = c · ε i j k`. -/
theorem strC_table (i j k : Fin 3) : strC h3 i j k = structConst h3 * ε i j k := by
  have hc := strC_cyc hinv h3
  have hs := strC_swap h3
  have h1 := strC_same₁ h3
  have h2 := strC_same₂ hinv h3
  have h3' : ∀ i j, strC h3 i j i = 0 := fun i j => by rw [hc, h2]
  have h012 : strC h3 0 1 2 = structConst h3 := rfl
  have h120 : strC h3 1 2 0 = structConst h3 := (hc 0 1 2).symm
  have h201 : strC h3 2 0 1 = structConst h3 := by rw [← hc 1 2 0, h120]
  have h102 : strC h3 1 0 2 = -structConst h3 := by rw [hs 0 1 2, h012]
  have h021 : strC h3 0 2 1 = -structConst h3 := by rw [hs 2 0 1, h201]
  have h210 : strC h3 2 1 0 = -structConst h3 := by rw [hs 1 2 0, h120]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [ε, h012, h120, h201, h102, h021, h210, h1, h2, h3']

include hinv in
/-- **Fórmula clave: `⁅x, y⁆ = c · (x × y)` en coordenadas ortonormales.** -/
theorem coords_bracket (x y : 𝔤) :
    coords h3 ⁅x, y⁆ = structConst h3 • crossProduct (coords h3 x) (coords h3 y) := by
  funext k
  have expand : coords h3 ⁅x, y⁆ k =
      inner ℝ (onb3 h3 k) ⁅∑ i, coords h3 x i • onb3 h3 i, ∑ j, coords h3 y j • onb3 h3 j⁆ := by
    rw [sum_coords_smul, sum_coords_smul]; rfl
  rw [expand]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, inner_sum, inner_smul_right]
  have hstr : ∀ i j, inner ℝ (onb3 h3 k) ⁅onb3 h3 i, onb3 h3 j⁆ = structConst h3 * ε i j k :=
    fun i j => strC_table hinv h3 i j k
  simp only [hstr, Fin.sum_univ_three]
  fin_cases k <;> simp [ε, cross_apply] <;> ring

include hinv in
/-- Si `c = 0` el álgebra es abeliana. -/
theorem isLieAbelian_of_structConst_eq_zero (hc : structConst h3 = 0) : IsLieAbelian 𝔤 := by
  constructor
  intro x y
  have h := coords_bracket hinv h3 x y
  rw [hc, zero_smul] at h
  apply eq_of_coords_eq h3
  intro i
  rw [h]
  simp [coords]

/-- El isomorfismo lineal `x ↦ c · coords x`. -/
def toModelLinear (c : ℝ) : 𝔤 →ₗ[ℝ] su2Model where
  toFun x := su2Model.ofVec (c • coords h3 x)
  map_add' x y := by
    apply su2Model.vec_injective
    rw [su2Model.vec_add, su2Model.vec_ofVec, su2Model.vec_ofVec, su2Model.vec_ofVec,
      coords_add, smul_add]
  map_smul' t x := by
    apply su2Model.vec_injective
    rw [RingHom.id_apply, su2Model.vec_smul, su2Model.vec_ofVec, su2Model.vec_ofVec,
      coords_smul, smul_comm]

theorem toModelLinear_apply (c : ℝ) (x : 𝔤) :
    su2Model.vec (toModelLinear h3 c x) = c • coords h3 x := rfl

include hinv h3 in
/-- **Paso 2: `𝔤 ≅ 𝔰𝔲(2)` como álgebras de Lie.** -/
theorem exists_lieEquiv_su2Model (hna : ¬ IsLieAbelian 𝔤) :
    Nonempty (𝔤 ≃ₗ⁅ℝ⁆ su2Model) := by
  have hc0 : structConst h3 ≠ 0 :=
    fun h => hna (isLieAbelian_of_structConst_eq_zero hinv h3 h)
  let f : 𝔤 →ₗ⁅ℝ⁆ su2Model :=
    { toModelLinear h3 (structConst h3) with
      map_lie' := by
        intro x y
        apply su2Model.vec_injective
        change su2Model.vec (toModelLinear h3 (structConst h3) ⁅x, y⁆) =
          su2Model.vec ⁅toModelLinear h3 (structConst h3) x, toModelLinear h3 (structConst h3) y⁆
        rw [su2Model.vec_bracket, toModelLinear_apply, toModelLinear_apply, toModelLinear_apply,
          coords_bracket hinv h3]
        simp only [map_smul, LinearMap.smul_apply, smul_smul] }
  refine ⟨LieEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y hxy
    have h := congrArg su2Model.vec hxy
    change su2Model.vec (toModelLinear h3 (structConst h3) x) =
      su2Model.vec (toModelLinear h3 (structConst h3) y) at h
    rw [toModelLinear_apply, toModelLinear_apply] at h
    apply eq_of_coords_eq h3
    intro i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc0 this
  · intro v
    refine ⟨∑ i, ((structConst h3)⁻¹ * su2Model.vec v i) • onb3 h3 i, ?_⟩
    apply su2Model.vec_injective
    change su2Model.vec (toModelLinear h3 (structConst h3) _) = su2Model.vec v
    rw [toModelLinear_apply]
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, coords, inner_sum, inner_smul_right]
    rw [Finset.sum_eq_single k]
    · rw [(orthonormal_iff_ite.mp (onb3 h3).orthonormal) k k]
      simp [hc0]
    · intro i _ hi
      rw [(orthonormal_iff_ite.mp (onb3 h3).orthonormal) k i]
      simp [Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_univ k) h

end ThreeDim

/-! ## Axioma 3: teoremas de Lie -/

/-- **AXIOMA 3.** Un grupo de Lie compacto conexo `G` cuya álgebra de Lie es `𝔰𝔲(2)` es
isomorfo (como grupo topológico) a `SU(2)` o a `SO(3)`: `G` es cociente del recubridor
universal `SU(2) ≅ S³` por un subgrupo discreto central, y `Z(SU(2)) = {±1}`. Mathlib no
dispone del tercer teorema de Lie ni de la teoría de recubrimientos de grupos de Lie. -/
axiom lie_group_of_su2 (S : LieStructure) [CompactSpace S.G] [ConnectedSpace S.G]
    (h : Nonempty (S.𝔤 ≃ₗ⁅ℝ⁆ su2Model)) :
    Nonempty (S.G ≃ₜ* SU2) ∨ Nonempty (S.G ≃ₜ* SO3)

/-! ## El teorema de clasificación -/

/-- **TEOREMA DE CLASIFICACIÓN (Etapa 2).** Para toda estructura `(P, G)` con `G` grupo
de Lie compacto conexo, `𝔤` simple y `Ad` transitiva sobre la esfera unidad de `𝔤`:
(1) `dim 𝔤 = 3`; (2) `𝔤 ≅ 𝔰𝔲(2)`; (3) `G ≅ SU(2)` o `G ≅ SO(3)`.
Depende de los axiomas 1–3; los pasos aritmético y algebraico están probados. -/
theorem clasificacion (S : LieStructure) [CompactSpace S.G] [ConnectedSpace S.G]
    [hs : LieAlgebra.IsSimple ℝ S.𝔤] (htrans : AdTransitive S) :
    Module.finrank ℝ S.𝔤 = 3 ∧
    Nonempty (S.𝔤 ≃ₗ⁅ℝ⁆ su2Model) ∧
    (Nonempty (S.G ≃ₜ* SU2) ∨ Nonempty (S.G ≃ₜ* SO3)) := by
  have h3 := finrank_eq_three S htrans
  have hiso := exists_lieEquiv_su2Model S.inner_bracket h3 hs.non_abelian
  exact ⟨h3, hiso, lie_group_of_su2 S hiso⟩

end Compila
