/-
# ETAPA 3 — CONVERGENCIA DE LAS CUATRO EXIGENCIAS

Definimos cuatro predicados `A1`–`A4` («exigencias») y siete predicados
`C1`–`C5`, `DR`, `Continuo` («propiedades») sobre estructuras `(P, G)` con `G` grupo de
Lie (interfaz `LieStructure` de la etapa 2), y probamos

  `(A1 ∧ A2 ∧ A3 ∧ A4) ↔ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ DR ∧ Continuo)`

para todo `G` conexo, junto con el corolario: toda estructura que cumple `A1`–`A4` es
`SU(2)` o `SO(3)`.

## Elecciones de definición (véase `ETAPA3.md`)

* **A1 Clausura**: `G` compacto y cerrado bajo su operación.
* **A2 Convergencia sin partir**: `P` es un singleton, `G` es infinito, todo `g` fija
  el mismo `∗`, y `𝔤` es simple.
* **A3 Relieve**: `𝔤 ≠ 0`; existen elementos no triviales **no conjugados** («distinta
  magnitud»); y `G` tiene **curvatura seccional constante positiva**. Mathlib no define
  la curvatura seccional; usamos la fórmula clásica para métricas bi-invariantes,
  `K(x, y) = ¼ ‖⁅x, y⁆‖² / (‖x‖²‖y‖² − ⟪x, y⟫²)`, de modo que «curvatura constante `κ > 0`»
  es la identidad `‖⁅x, y⁆‖² = 4κ (‖x‖²‖y‖² − ⟪x, y⟫²)` para todo `x, y ∈ 𝔤`.
* **A4 Isotropía**: `Ad` es transitiva sobre la esfera unidad de `𝔤`.
* **C5 Atemporalidad**: ningún orden total estricto sobre `G` es invariante por la
  operación (no hay «flecha del tiempo»).
* **Continuo**: `G` es conexo (la estructura de variedad `C^∞` es parte de los datos).
-/
import Compila.Etapa2

open Matrix Quaternion
open scoped Manifold ContDiff

noncomputable section

namespace Compila

namespace LieStructure

variable (S : LieStructure)

/-! ## Las cuatro exigencias -/

/-- **A1 Clausura**: `G` es compacto y cerrado bajo su operación (nada remite fuera de `G`). -/
def A1 : Prop := CompactSpace S.G ∧ ∀ g h : S.G, ∃ k : S.G, g * h = k

/-- **A2 Convergencia sin partir**: un solo centro `∗`, infinitas lecturas, todas leen el
mismo `∗`, y el álgebra de Lie es simple (no se parte). -/
def A2 : Prop :=
  (Subsingleton S.P ∧ Nonempty S.P) ∧ Infinite S.G ∧
  (∀ (g : S.G) (p : S.P), g • p = p) ∧ LieAlgebra.IsSimple ℝ S.𝔤

/-- Curvatura seccional constante positiva `κ` de la métrica bi-invariante:
`‖⁅x, y⁆‖² = 4κ (‖x‖²‖y‖² − ⟪x, y⟫²)`. -/
def ConstantPositiveCurvature : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ x y : S.𝔤,
    ‖⁅x, y⁆‖ ^ 2 = 4 * κ * (‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y : ℝ) ^ 2)

/-- **A3 Relieve**: el paso de lo total a lo restringido tiene geometría. -/
def A3 : Prop :=
  Nontrivial S.𝔤 ∧
  (∃ g h : S.G, g ≠ 1 ∧ h ≠ 1 ∧ ¬ IsConj g h) ∧
  S.ConstantPositiveCurvature

/-- **A4 Isotropía**: ninguna dirección del álgebra de Lie viene favorecida. -/
def A4 : Prop := AdTransitive S

/-! ## Las propiedades de la etapa 1 como predicados -/

/-- **C1 Isotropía direccional**: `Ad` transitiva sobre las direcciones unitarias. -/
def C1 : Prop := AdTransitive S

/-- **C2 Indivisibilidad**: `𝔤` simple. -/
def C2 : Prop := LieAlgebra.IsSimple ℝ S.𝔤

/-- **C3 Homogeneidad**: `G` actúa transitivamente sobre sí mismo. -/
def C3 : Prop := MulAction.IsPretransitive S.G S.G

/-- **C4 Autosuficiencia**: compacto y cerrado bajo la operación. -/
def C4 : Prop := CompactSpace S.G ∧ ∀ g h : S.G, ∃ k : S.G, g * h = k

/-- **C5 Atemporalidad**: sin orden total invariante. -/
def C5 : Prop := ∀ r : S.G → S.G → Prop, ¬ IsInvariantTotalOrder r

/-- **DR Doble registro**: `P` singleton, `G` infinito. -/
def DR : Prop := (Subsingleton S.P ∧ Nonempty S.P) ∧ Infinite S.G

/-- **Continuo**: `G` es una variedad diferenciable (dato de la estructura) conexa. -/
def Continuo : Prop := ConnectedSpace S.G

end LieStructure

/-! ## Lemas auxiliares -/

/-- `-1 ∈ SO(3)` no existe, pero `diag(1, −1, −1)` es una involución no trivial. -/
def rotπ : SO3 :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose]
    · simp [Matrix.det_fin_three]⟩

/-- Rotación de 90° alrededor del eje `z`. -/
def rot90 : SO3 :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose]
    · simp [Matrix.det_fin_three]⟩

theorem rotπ_ne_one : rotπ ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg Subtype.val h) 1) 1
  norm_num [rotπ] at this

theorem rotπ_mul_self : rotπ * rotπ = 1 := by
  apply Subtype.ext
  change (!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) ℝ) * !![1, 0, 0; 0, -1, 0; 0, 0, -1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem rot90_ne_one : rot90 ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  norm_num [rot90] at this

/-- Elementos conjugados de `SO(3)` tienen la misma traza. -/
theorem trace_eq_of_isConj_SO3 {a b : SO3} (h : IsConj a b) :
    (a : Matrix (Fin 3) (Fin 3) ℝ).trace = (b : Matrix (Fin 3) (Fin 3) ℝ).trace := by
  rw [isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  have hc' := congrArg Subtype.val hc
  simp only [Submonoid.coe_mul] at hc'
  have hinv : ((c⁻¹ : SO3) : Matrix (Fin 3) (Fin 3) ℝ) = star (c : Matrix (Fin 3) (Fin 3) ℝ) := rfl
  rw [hinv] at hc'
  have hcc : star (c : Matrix (Fin 3) (Fin 3) ℝ) * c = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp c.2).1
  rw [← hc', Matrix.trace_mul_comm, ← mul_assoc, hcc, one_mul]

theorem not_isConj_rotπ_rot90 : ¬ IsConj rotπ rot90 := by
  intro h
  have := trace_eq_of_isConj_SO3 h
  simp [rotπ, rot90, Matrix.trace_fin_three] at this
  norm_num at this

/-- En `S³`, `-1` es central: no es conjugado de `i`. -/
theorem not_isConj_negOne_i_S3 : ¬ IsConj negOneS3 iS3 := by
  intro h
  rw [isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  have hc' := congrArg (fun x : S3 => (x : ℍ)) hc
  simp only [Metric.unitSphere.coe_mul, coe_inv_S3, negOneS3, iS3] at hc'
  rw [mul_neg, mul_one, neg_mul, self_mul_star_of_mem_S3] at hc'
  have := congrArg QuaternionAlgebra.imI hc'
  norm_num at this

/-- Transporte de la no conjugación a lo largo de un isomorfismo de grupos. -/
theorem not_isConj_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a b : H}
    (h : ¬ IsConj a b) : ¬ IsConj (e.symm a) (e.symm b) := by
  intro h'
  apply h
  have := e.toMonoidHom.map_isConj h'
  simpa using this

/-! ## Curvatura constante en dimensión 3 (probado) -/

section Curvature

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
  [LieBracketOn 𝔤] [LieBracketSMul ℝ 𝔤]
  (hinv : ∀ x y z : 𝔤, (inner ℝ ⁅x, y⁆ z : ℝ) = inner ℝ x ⁅y, z⁆)
  (h3 : Module.finrank ℝ 𝔤 = 3)

theorem inner_eq_sum_coords (x y : 𝔤) :
    (inner ℝ x y : ℝ) = ∑ i, coords h3 x i * coords h3 y i := by
  rw [← (onb3 h3).sum_inner_mul_inner x y]
  simp only [coords, real_inner_comm]

theorem norm_sq_eq_sum_coords (x : 𝔤) : ‖x‖ ^ 2 = ∑ i, coords h3 x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_coords h3]
  simp [sq]

include hinv h3 in
/-- **Curvatura seccional constante positiva** en toda álgebra de Lie real de dimensión 3,
no abeliana, con producto interior invariante: `‖⁅x, y⁆‖² = c² (‖x‖²‖y‖² − ⟪x, y⟫²)`
(identidad de Lagrange para el producto vectorial). -/
theorem constant_curvature (hna : ¬ IsLieAbelian 𝔤) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x y : 𝔤,
      ‖⁅x, y⁆‖ ^ 2 = 4 * κ * (‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y : ℝ) ^ 2) := by
  have hc0 : structConst h3 ≠ 0 :=
    fun h => hna (isLieAbelian_of_structConst_eq_zero hinv h3 h)
  refine ⟨structConst h3 ^ 2 / 4, by positivity, fun x y => ?_⟩
  rw [norm_sq_eq_sum_coords h3, norm_sq_eq_sum_coords h3, norm_sq_eq_sum_coords h3,
    inner_eq_sum_coords h3, coords_bracket hinv h3]
  simp only [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, cross_apply]
  simp
  ring

end Curvature

/-! ## El teorema de convergencia -/

namespace LieStructure

variable (S : LieStructure)

/-- Consecuencia de la clasificación: `G` contiene una involución no trivial y dos
elementos no triviales no conjugados. -/
theorem involution_and_nonconj [CompactSpace S.G] [ConnectedSpace S.G]
    [LieAlgebra.IsSimple ℝ S.𝔤] (htrans : AdTransitive S) :
    (∃ g : S.G, g ≠ 1 ∧ g * g = 1) ∧ (∃ g h : S.G, g ≠ 1 ∧ h ≠ 1 ∧ ¬ IsConj g h) := by
  obtain ⟨-, -, hG⟩ := clasificacion S htrans
  rcases hG with hL | hR
  · -- `G ≅ SU(2) ≅ S³`
    obtain ⟨e⟩ := hL
    let f : S.G ≃* S3 := e.toMulEquiv.trans ψ.symm
    refine ⟨⟨f.symm negOneS3, ?_, ?_⟩, f.symm negOneS3, f.symm iS3, ?_, ?_,
      not_isConj_of_equiv f not_isConj_negOne_i_S3⟩
    · intro h
      apply negOneS3_ne_one
      simpa using congrArg f h
    · rw [← map_mul, negOneS3_mul_self, map_one]
    · intro h
      apply negOneS3_ne_one
      simpa using congrArg f h
    · intro h
      have := congrArg f h
      simp only [MulEquiv.apply_symm_apply, map_one] at this
      have := congrArg (fun x : S3 => (x : ℍ).imI) this
      norm_num [iS3] at this
  · -- `G ≅ SO(3)`
    obtain ⟨e⟩ := hR
    let f : S.G ≃* SO3 := e.toMulEquiv
    refine ⟨⟨f.symm rotπ, ?_, ?_⟩, f.symm rotπ, f.symm rot90, ?_, ?_,
      not_isConj_of_equiv f not_isConj_rotπ_rot90⟩
    · intro h
      apply rotπ_ne_one
      simpa using congrArg f h
    · rw [← map_mul, rotπ_mul_self, map_one]
    · intro h
      apply rotπ_ne_one
      simpa using congrArg f h
    · intro h
      apply rot90_ne_one
      simpa using congrArg f h

/-- **Dirección (→): las cuatro exigencias implican las siete propiedades.**
Todo es desempaquetado de definiciones salvo `C5`, que se obtiene de la clasificación
(etapa 2): `G ≅ SU(2)` o `SO(3)` contiene una involución, luego no admite órdenes
invariantes. -/
theorem convergencia_mp [ConnectedSpace S.G] (h : S.A1 ∧ S.A2 ∧ S.A3 ∧ S.A4) :
    S.C1 ∧ S.C2 ∧ S.C3 ∧ S.C4 ∧ S.C5 ∧ S.DR ∧ S.Continuo := by
  obtain ⟨⟨hcompact, hclosed⟩, ⟨hP, hinf, -, hsimple⟩, -, htrans⟩ := h
  have : CompactSpace S.G := hcompact
  have : LieAlgebra.IsSimple ℝ S.𝔤 := hsimple
  refine ⟨htrans, hsimple, ⟨fun x y => ⟨y * x⁻¹, by simp⟩⟩, ⟨hcompact, hclosed⟩, ?_,
    ⟨hP, hinf⟩, ‹ConnectedSpace S.G›⟩
  -- C5
  intro r hr
  obtain ⟨⟨g, hg1, hg2⟩, -⟩ := S.involution_and_nonconj htrans
  exact no_invariant_order_of_involution g hg1 hg2 r hr

/-- **Dirección (←): las siete propiedades implican las cuatro exigencias.**
`A1`, `A2`, `A4` son desempaquetado; `A3` tiene contenido real: la no trivialidad de `𝔤`
sale de la simplicidad, los elementos no conjugados de la clasificación (etapa 2) y la
curvatura constante positiva del teorema `constant_curvature` (dimensión 3 + métrica
invariante + no abeliana ⇒ identidad de Lagrange). -/
theorem convergencia_mpr [ConnectedSpace S.G]
    (h : S.C1 ∧ S.C2 ∧ S.C3 ∧ S.C4 ∧ S.C5 ∧ S.DR ∧ S.Continuo) :
    S.A1 ∧ S.A2 ∧ S.A3 ∧ S.A4 := by
  obtain ⟨htrans, hsimple, -, ⟨hcompact, hclosed⟩, -, ⟨hP, hinf⟩, -⟩ := h
  have : CompactSpace S.G := hcompact
  have : LieAlgebra.IsSimple ℝ S.𝔤 := hsimple
  refine ⟨⟨hcompact, hclosed⟩, ⟨hP, hinf, fun g p => hP.1.elim _ _, hsimple⟩, ?_, htrans⟩
  have h3 := finrank_eq_three S htrans
  refine ⟨?_, (S.involution_and_nonconj htrans).2, ?_⟩
  · -- 𝔤 no trivial
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hsimple.non_abelian ⟨fun x y => Subsingleton.elim _ _⟩
  · exact constant_curvature S.inner_bracket h3 hsimple.non_abelian

/-- **TEOREMA DE CONVERGENCIA (Etapa 3).** Para toda estructura `(P, G)` con `G` grupo de
Lie conexo: `(A1 ∧ A2 ∧ A3 ∧ A4) ↔ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ DR ∧ Continuo)`. -/
theorem convergencia [ConnectedSpace S.G] :
    (S.A1 ∧ S.A2 ∧ S.A3 ∧ S.A4) ↔ (S.C1 ∧ S.C2 ∧ S.C3 ∧ S.C4 ∧ S.C5 ∧ S.DR ∧ S.Continuo) :=
  ⟨S.convergencia_mp, S.convergencia_mpr⟩

/-- **COROLARIO.** Toda estructura `(P, G)` con `G` grupo de Lie conexo que cumple
`A1`–`A4` tiene `G ≅ SU(2)` o `G ≅ SO(3)` (y `𝔤 ≅ 𝔰𝔲(2)`). -/
theorem corolario [ConnectedSpace S.G] (h : S.A1 ∧ S.A2 ∧ S.A3 ∧ S.A4) :
    Nonempty (S.𝔤 ≃ₗ⁅ℝ⁆ su2Model) ∧ (Nonempty (S.G ≃ₜ* SU2) ∨ Nonempty (S.G ≃ₜ* SO3)) := by
  obtain ⟨⟨hcompact, -⟩, ⟨-, -, -, hsimple⟩, -, htrans⟩ := h
  have : CompactSpace S.G := hcompact
  have : LieAlgebra.IsSimple ℝ S.𝔤 := hsimple
  obtain ⟨-, h2, h3⟩ := clasificacion S htrans
  exact ⟨h2, h3⟩

end LieStructure

/-! ## Existencia: `S³ ≅ SU(2)` como `LieStructure` que cumple `A1`–`A4` (sin axiomas) -/

/-- Acción trivial de cualquier grupo sobre el punto `∗`. -/
instance instMulActionUnit {G : Type*} [Group G] : MulAction G Unit where
  smul _ _ := ()
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- La estructura `F = ({∗}, S³)` del tratado. -/
def S3Structure : LieStructure where
  P := Unit
  G := S3
  n := 3
  𝔤 := ImH
  finrank_eq := finrank_ImH
  Ad := AdS3
  Ad_bracket := AdS3_bracket
  inner_bracket := ImH.inner_bracket

theorem S3Structure_A1 : S3Structure.A1 :=
  ⟨(inferInstance : CompactSpace S3), fun g h => ⟨g * h, rfl⟩⟩

theorem S3Structure_A2 : S3Structure.A2 :=
  ⟨⟨(inferInstance : Subsingleton Unit), (inferInstance : Nonempty Unit)⟩,
    (inferInstance : Infinite S3), fun _ _ => rfl, ImH.isSimple⟩

theorem S3Structure_A4 : S3Structure.A4 := AdS3_transitive

/-- `A3` para `S³`, probado **directamente** (sin los axiomas de la etapa 2). -/
theorem iS3_ne_one : iS3 ≠ 1 := by
  intro h
  have := congrArg (fun x : S3 => (x : ℍ).imI) h
  simp [iS3] at this

theorem ImH.nontrivial : Nontrivial ImH :=
  ⟨⟨0, ⟨⟨0, 1, 0, 0⟩, by rw [mem_ImH]⟩, fun h => by
    have := congrArg (fun x : ImH => (x : ℍ).imI) h
    simp at this⟩⟩

theorem S3Structure_A3 : S3Structure.A3 :=
  ⟨ImH.nontrivial, ⟨negOneS3, iS3, negOneS3_ne_one, iS3_ne_one, not_isConj_negOne_i_S3⟩,
    constant_curvature ImH.inner_bracket finrank_ImH ImH.isSimple.non_abelian⟩

/-- **Existencia**: la estructura `({∗}, S³ ≅ SU(2))` cumple las cuatro exigencias. -/
theorem S3Structure_A : S3Structure.A1 ∧ S3Structure.A2 ∧ S3Structure.A3 ∧ S3Structure.A4 :=
  ⟨S3Structure_A1, S3Structure_A2, S3Structure_A3, S3Structure_A4⟩

end Compila
