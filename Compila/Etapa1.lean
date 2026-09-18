/-
# ETAPA 1 — EXISTENCIA

Formalización en Lean 4 + Mathlib de las propiedades del fundamento
`F = (P, G)` con `P = {∗}` y `G = SU(2)`.

Modelamos `SU(2)` de dos maneras equivalentes:

* `SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ` — el grupo de matrices 2×2
  unitarias de determinante 1 (definición estándar de Mathlib).
* `S3 := Metric.sphere (0 : ℍ) 1` — los cuaterniones unitarios.

Probamos que ambos son isomorfos como grupos topológicos (`ψ : S3 ≃ₜ* SU2`),
de modo que toda propiedad probada en un modelo se transporta al otro.
El álgebra de Lie `𝔰𝔲(2)` se modela como los cuaterniones puros `ImH`
(parte real nula) con el corchete conmutador `⁅x, y⁆ = x * y - y * x`.

Convención de estados usada en `ETAPA1.md`:
`PROBADO` (sin `sorry`), `ADMITIDO` (con `sorry` y explicación), `TRIVIAL`.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Order.Interval.Set.Infinite

open Matrix Quaternion
open scoped Manifold ContDiff

noncomputable section

namespace Compila

/-! ## Corchetes de Lie sobre un grupo abeliano dado

Para poder combinar `LieRing` con `NormedAddCommGroup`/`InnerProductSpace` sobre el mismo
tipo sin crear un «diamante» de instancias (dos estructuras de grupo aditivo distintas),
introducimos la clase `LieBracketOn`, que añade un corchete a un grupo abeliano **ya dado**
y deriva de ella las instancias `LieRing` y `LieAlgebra` de Mathlib. -/

/-- Un corchete de Lie sobre el grupo abeliano `L` (dado). -/
class LieBracketOn (L : Type*) [AddCommGroup L] where
  bracket : L → L → L
  add_lie : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  lie_add : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  lie_self : ∀ x, bracket x x = 0
  leibniz_lie : ∀ x y z,
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z)

instance LieBracketOn.toLieRing (L : Type*) [AddCommGroup L] [LieBracketOn L] : LieRing L where
  bracket := LieBracketOn.bracket
  add_lie := LieBracketOn.add_lie
  lie_add := LieBracketOn.lie_add
  lie_self := LieBracketOn.lie_self
  leibniz_lie := LieBracketOn.leibniz_lie

/-- Compatibilidad del corchete con la estructura de `R`-módulo (dada). -/
class LieBracketSMul (R L : Type*) [CommRing R] [AddCommGroup L] [Module R L]
    [LieBracketOn L] : Prop where
  lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆

instance LieBracketSMul.toLieAlgebra (R L : Type*) [CommRing R] [AddCommGroup L] [Module R L]
    [LieBracketOn L] [LieBracketSMul R L] : LieAlgebra R L :=
  ⟨LieBracketSMul.lie_smul⟩

/-! ## Los dos modelos de `G` -/

/-- `SU(2)` como grupo de matrices complejas 2×2 unitarias de determinante 1. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- `S³`: los cuaterniones de norma 1. Es un grupo (instancia de Mathlib). -/
abbrev S3 := Metric.sphere (0 : ℍ) 1

/-! ## Utilidades sobre cuaterniones -/

theorem normSq_eq_one_of_mem_S3 (q : S3) : normSq (q : ℍ) = 1 := by
  rw [normSq_eq_norm_mul_self, mem_sphere_zero_iff_norm.1 q.2, one_mul]

theorem mem_S3_iff_normSq {q : ℍ} : q ∈ S3 ↔ normSq q = 1 := by
  rw [mem_sphere_zero_iff_norm, normSq_eq_norm_mul_self]
  constructor
  · intro h; rw [h, one_mul]
  · intro h
    have := norm_nonneg q
    nlinarith

theorem star_mul_self_of_mem_S3 (q : S3) : star (q : ℍ) * q = 1 := by
  rw [star_mul_self, normSq_eq_one_of_mem_S3]; simp

theorem self_mul_star_of_mem_S3 (q : S3) : (q : ℍ) * star (q : ℍ) = 1 := by
  rw [self_mul_star, normSq_eq_one_of_mem_S3]; simp

theorem inv_coe_S3 (q : S3) : (q : ℍ)⁻¹ = star (q : ℍ) := by
  rw [Quaternion.inv_def, normSq_eq_one_of_mem_S3]; simp

theorem coe_inv_S3 (q : S3) : ((q⁻¹ : S3) : ℍ) = star (q : ℍ) := by
  rw [Metric.unitSphere.coe_inv, inv_coe_S3]

/-! ## El isomorfismo `S³ ≅ SU(2)`

`q = a + b i + c j + d k ↦ [[a + b i, c + d i], [−c + d i, a − b i]]`. -/

/-- Representación matricial de un cuaternión. -/
def toMat (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

theorem toMat_one : toMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, Complex.ext_iff]

theorem toMat_mul (p q : ℍ) : toMat (p * q) = toMat p * toMat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    (try constructor) <;> ring

theorem toMat_star (q : ℍ) : toMat (star q) = (toMat q)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem det_toMat (q : ℍ) : (toMat q).det = ((normSq q : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  constructor
  · simp [toMat, Matrix.det_fin_two_of]
    rw [normSq_def']; ring
  · simp [toMat, Matrix.det_fin_two_of]; ring

theorem toMat_injective : Function.Injective toMat := by
  intro p q h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [toMat, Complex.ext_iff] at h00 h01
  ext <;> tauto

theorem continuous_complex_mk {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => (⟨f x, g x⟩ : ℂ) := by
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

theorem continuous_toMat : Continuous toMat := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_complex_mk continuous_re continuous_imI
  · exact continuous_complex_mk continuous_imJ continuous_imK
  · exact continuous_complex_mk continuous_imJ.neg continuous_imK
  · exact continuous_complex_mk continuous_re continuous_imI.neg

theorem toMat_mem (q : S3) : toMat q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff,
    Matrix.star_eq_conjTranspose, ← toMat_star, ← toMat_mul, self_mul_star,
    normSq_eq_one_of_mem_S3, det_toMat, normSq_eq_one_of_mem_S3]
  simp [toMat_one]

/-- El homomorfismo `S³ →* SU(2)`. -/
def ψHom : S3 →* SU2 where
  toFun q := ⟨toMat q, toMat_mem q⟩
  map_one' := Subtype.ext (by simp [toMat_one])
  map_mul' p q := Subtype.ext (by simp [Metric.unitSphere.coe_mul, toMat_mul])

theorem ψHom_injective : Function.Injective ψHom := by
  intro p q h
  exact Subtype.ext (toMat_injective (congrArg Subtype.val h))

theorem ψHom_surjective : Function.Surjective ψHom := by
  rintro ⟨A, hA⟩
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff] at hA
  obtain ⟨hU, hdet⟩ := hA
  -- `star A = A⁻¹ = adjugate A` porque `det A = 1`
  have hinv : star A = A.adjugate := by
    rw [← Matrix.inv_eq_right_inv hU, Matrix.inv_def, hdet]; simp
  have e11 := congrFun (congrFun hinv 1) 1
  have e10 := congrFun (congrFun hinv 1) 0
  rw [Matrix.adjugate_fin_two] at e11 e10
  simp [Matrix.star_apply] at e11 e10
  -- e11 : star (A 1 1) = A 0 0,  e10 : star (A 0 1) = -A 1 0
  have e11' : A 1 1 = (starRingEnd ℂ) (A 0 0) := by rw [← e11, Complex.conj_conj]
  have e10' : A 1 0 = -(starRingEnd ℂ) (A 0 1) := by rw [e10, neg_neg]
  set q : ℍ := ⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩ with hq
  have hqA : toMat q = A := by
    rw [Matrix.eta_fin_two A, e11', e10']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, hq, Complex.ext_iff]
  have hqn : normSq q = 1 := by
    have := det_toMat q
    rw [hqA, hdet] at this
    exact_mod_cast this.symm
  refine ⟨⟨q, mem_S3_iff_normSq.mpr hqn⟩, Subtype.ext ?_⟩
  simpa [ψHom] using hqA

/-- **Isomorfismo de grupos** `S³ ≃* SU(2)`. -/
def ψ : S3 ≃* SU2 := MulEquiv.ofBijective ψHom ⟨ψHom_injective, ψHom_surjective⟩

theorem ψ_apply_coe (q : S3) : ((ψ q : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = toMat q := rfl

theorem continuous_ψ : Continuous ψ :=
  continuous_induced_rng.2 (continuous_toMat.comp continuous_subtype_val)

/-! ## Topología de `S³` y de `SU(2)` -/

instance : CompactSpace S3 := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

theorem one_lt_rank_H : 1 < Module.rank ℝ ℍ := by
  rw [(QuaternionAlgebra.rank_eq_four (-1 : ℝ) 0 (-1) : Module.rank ℝ ℍ = 4)]
  norm_num

instance : ConnectedSpace S3 :=
  isConnected_iff_connectedSpace.mp (isConnected_sphere one_lt_rank_H 0 zero_le_one)

/-- `ψ` como homeomorfismo (biyección continua de un compacto en un Hausdorff). -/
def ψHomeo : S3 ≃ₜ SU2 := Continuous.homeoOfEquivCompactToT2 (f := ψ.toEquiv) continuous_ψ

/-- **Bonus (parte algebraico-topológica): `S³ ≅ SU(2)` como grupos topológicos.** -/
def ψTop : S3 ≃ₜ* SU2 :=
  { ψ with
    continuous_toFun := continuous_ψ
    continuous_invFun := ψHomeo.symm.continuous }

/-- **C4 (compacidad): `SU(2)` es compacto.** -/
instance : CompactSpace SU2 := ψHomeo.compactSpace

/-- **Continuo (conexión): `SU(2)` es conexo.** -/
instance : ConnectedSpace SU2 := ψHomeo.connectedSpace_iff.mp inferInstance

/-- `SU(2)` es un grupo topológico (inversión = conjugada traspuesta, continua). -/
instance : IsTopologicalGroup SU2 where
  continuous_mul := continuous_mul
  continuous_inv := continuous_induced_rng.2 (by
    exact continuous_star.comp continuous_subtype_val)

/-- **C4 (clausura bajo la operación): `SU(2)` es cerrado bajo el producto (es un grupo).**
Trivial: la operación es total en `G`. -/
theorem C4_closed_under_mul (g h : SU2) : ∃ k : SU2, g * h = k := ⟨g * h, rfl⟩

/-- Demostración directa de compacidad (sin pasar por `S³`): `SU(2)` es un cerrado
acotado de `ℂ⁴`. -/
theorem isClosed_SU2 : IsClosed (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h1 : IsClosed (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    isClosed_unitary
  have h2 : IsClosed {A : Matrix (Fin 2) (Fin 2) ℂ | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  convert h1.inter h2 using 1
  ext A
  simp [Matrix.mem_specialUnitaryGroup_iff]

theorem isCompact_SU2 : IsCompact (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine IsCompact.of_isClosed_subset (s := Set.pi Set.univ fun _ : Fin 2 =>
    Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : ℂ) 1) ?_ isClosed_SU2 ?_
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
  · intro A hA
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary (Matrix.mem_specialUnitaryGroup_iff.mp hA).1 i j

/-! ## C3 — Homogeneidad: `G` actúa transitivamente sobre sí mismo -/

/-- **C3: `SU(2)` actúa transitivamente sobre sí mismo por multiplicación.** -/
instance : MulAction.IsPretransitive SU2 SU2 :=
  ⟨fun x y => ⟨y * x⁻¹, by simp⟩⟩

instance : MulAction.IsPretransitive S3 S3 :=
  ⟨fun x y => ⟨y * x⁻¹, by simp⟩⟩

/-! ## DR — Doble registro: `P` es un punto y `G` es infinito -/

/-- El punto único `∗`. -/
abbrev P := Unit

/-- **DR (métrica nula): `P` es un singleton.** -/
theorem DR_P_subsingleton : Subsingleton P ∧ Nonempty P := ⟨inferInstance, inferInstance⟩

/-- La curva `t ↦ t + √(1 - t²) i` en `S³`, inyectiva sobre `[-1, 1]`. -/
def arc (t : Set.Icc (-1 : ℝ) 1) : S3 :=
  ⟨⟨t, Real.sqrt (1 - (t : ℝ) ^ 2), 0, 0⟩, by
    rw [mem_S3_iff_normSq, normSq_def']
    have ht : 0 ≤ 1 - (t : ℝ) ^ 2 := by
      obtain ⟨t, h1, h2⟩ := t
      simp only
      nlinarith
    simp [Real.sq_sqrt ht]⟩

theorem arc_injective : Function.Injective arc := by
  intro s t h
  have := congrArg (fun x : S3 => (x : ℍ).re) h
  exact Subtype.ext (by simpa [arc] using this)

/-- **DR (contraste no nulo): `S³` es infinito.** -/
instance : Infinite S3 :=
  haveI : Infinite (Set.Icc (-1 : ℝ) 1) :=
    Set.infinite_coe_iff.mpr (Set.Icc_infinite (by norm_num))
  Infinite.of_injective arc arc_injective

/-- **DR (contraste no nulo): `SU(2)` es infinito.** -/
instance : Infinite SU2 := Infinite.of_injective ψ ψ.injective

/-! ## Polaridad: existe `g` con `g ≠ g⁻¹` -/

/-- El cuaternión `i` como elemento de `S³`. -/
def iS3 : S3 := ⟨⟨0, 1, 0, 0⟩, by rw [mem_S3_iff_normSq, normSq_def']; norm_num⟩

theorem iS3_ne_inv : iS3 ≠ iS3⁻¹ := by
  intro h
  have := congrArg (fun x : S3 => (x : ℍ).imI) h
  simp only [coe_inv_S3, iS3] at this
  norm_num at this

/-- **Polaridad en `S³`.** -/
theorem polaridad_S3 : ∃ g : S3, g ≠ g⁻¹ := ⟨iS3, iS3_ne_inv⟩

/-- **Polaridad en `SU(2)`: existe `g ∈ SU(2)` con `g ≠ g⁻¹`.** -/
theorem polaridad_SU2 : ∃ g : SU2, g ≠ g⁻¹ :=
  ⟨ψ iS3, fun h => iS3_ne_inv (ψ.injective (by rw [map_inv]; exact h))⟩

/-! ## C5 — Atemporalidad

La estructura `F = (P, G)` consta únicamente de un punto y un grupo; no contiene
ningún orden total distinguido. Lo formalizamos con contenido: **ningún** orden total
estricto sobre `G` es invariante por la operación del grupo (no hay «flecha del
tiempo» compatible con la composición de lecturas). La razón es que `G` contiene una
involución no trivial (`-1`), y un grupo con torsión no admite órdenes invariantes. -/

/-- Un orden total estricto invariante por traslación a la izquierda. -/
def IsInvariantTotalOrder {G : Type*} [Group G] (r : G → G → Prop) : Prop :=
  IsStrictTotalOrder G r ∧ ∀ a b c : G, r b c → r (a * b) (a * c)

/-- Lema general: un grupo con una involución no trivial no admite órdenes totales
invariantes. -/
theorem no_invariant_order_of_involution {G : Type*} [Group G] (g : G) (hg : g ≠ 1)
    (hg2 : g * g = 1) (r : G → G → Prop) (hr : IsInvariantTotalOrder r) : False := by
  obtain ⟨hord, hinv⟩ := hr
  rcases trichotomous_of r g 1 with h | h | h
  · have h' := hinv g g 1 h
    rw [hg2, mul_one] at h'
    exact irrefl_of r _ (trans_of r h' h)
  · exact hg h
  · have h' := hinv g 1 g h
    rw [mul_one, hg2] at h'
    exact irrefl_of r _ (trans_of r h h')

/-- `-1 ∈ S³`. -/
def negOneS3 : S3 := ⟨-1, by rw [mem_S3_iff_normSq]; simp⟩

theorem negOneS3_ne_one : negOneS3 ≠ 1 := by
  intro h
  have := congrArg (fun x : S3 => (x : ℍ).re) h
  norm_num [negOneS3] at this

theorem negOneS3_mul_self : negOneS3 * negOneS3 = 1 := by
  apply Subtype.ext
  simp [negOneS3, Metric.unitSphere.coe_mul]

/-- **C5 en `S³`: no existe ningún orden total invariante en `G`.** -/
theorem C5_S3 : ∀ r : S3 → S3 → Prop, ¬ IsInvariantTotalOrder r :=
  fun r hr => no_invariant_order_of_involution negOneS3 negOneS3_ne_one negOneS3_mul_self r hr

/-- **C5 en `SU(2)`: no existe ningún orden total invariante en `G`.** -/
theorem C5_SU2 : ∀ r : SU2 → SU2 → Prop, ¬ IsInvariantTotalOrder r :=
  fun r hr => no_invariant_order_of_involution (ψ negOneS3)
    (fun h => negOneS3_ne_one (ψ.injective (by rw [map_one]; exact h)))
    (by rw [← map_mul, negOneS3_mul_self, map_one]) r hr

/-! ## Continuo — `S³` es una variedad diferenciable conexa y un grupo de Lie -/

instance factFinrankH : Fact (Module.finrank ℝ ℍ = 3 + 1) :=
  ⟨(QuaternionAlgebra.finrank_eq_four (-1 : ℝ) 0 (-1) : Module.finrank ℝ ℍ = 4)⟩

/-- `S³` es un espacio con cartas modelado en `ℝ³` (proyección estereográfica). -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S3 :=
  EuclideanSpace.instChartedSpaceSphere

/-- **Continuo: `S³` es una variedad analítica (en particular `C^∞`).** -/
instance : IsManifold (𝓡 3) ω S3 := EuclideanSpace.instIsManifoldSphere (E := ℍ)

/-- **`S³` es un grupo de Lie (analítico).** Multiplicación e inversión (= conjugación,
que es lineal) son analíticas. -/
instance : LieGroup (𝓡 3) ω S3 where
  contMDiff_mul := by
    apply ContMDiff.codRestrict_sphere
    let c : S3 → ℍ := (↑)
    have h₂ : ContMDiff (𝓘(ℝ, ℍ).prod 𝓘(ℝ, ℍ)) 𝓘(ℝ, ℍ) ω fun z : ℍ × ℍ => z.fst * z.snd := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn⟩
    suffices h₁ : ContMDiff _ _ _ (Prod.map c c) from h₂.comp h₁
    apply ContMDiff.prodMap <;> exact contMDiff_coe_sphere
  contMDiff_inv := by
    apply ContMDiff.codRestrict_sphere
    -- la conjugación `star` es `ℝ`-lineal: `star q = 2 re(q) − q`
    have hstar : ContDiff ℝ ω (fun q : ℍ => star q) := by
      have : (fun q : ℍ => star q) = fun q : ℍ =>
          (algebraMapCLM ℝ ℍ) (2 * (LinearMap.toContinuousLinearMap
            (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))) q) - q := by
        funext q
        rw [star_eq_two_re_sub]
        rfl
      rw [this]
      fun_prop
    simp only [inv_coe_S3]
    exact hstar.contMDiff.comp contMDiff_coe_sphere

/-! ## El álgebra de Lie `𝔰𝔲(2)` como cuaterniones puros -/

/-- Los cuaterniones puros (parte real nula): el álgebra de Lie de `S³ ≅ SU(2)`. -/
def ImH : Submodule ℝ ℍ := LinearMap.ker (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))

theorem mem_ImH {q : ℍ} : q ∈ ImH ↔ q.re = 0 := by
  simp [ImH, LinearMap.mem_ker, QuaternionAlgebra.reₗ]

theorem ImH.re_eq_zero (x : ImH) : (x : ℍ).re = 0 := mem_ImH.mp x.2

theorem ImH.star_coe (x : ImH) : star (x : ℍ) = -(x : ℍ) := star_eq_neg.mpr (ImH.re_eq_zero x)

theorem re_mul_comm (a b : ℍ) : (a * b).re = (b * a).re := by
  simp only [re_mul]; ring

/-- El conmutador de dos cuaterniones puros es puro. -/
theorem commutator_mem_ImH (x y : ImH) : (x : ℍ) * y - y * x ∈ ImH := by
  rw [mem_ImH, re_sub, re_mul_comm, sub_self]

/-- El corchete `⁅x, y⁆ = x y − y x` sobre los cuaterniones puros. -/
instance : LieBracketOn ImH where
  bracket x y := ⟨(x : ℍ) * y - y * x, commutator_mem_ImH x y⟩
  add_lie x y z := Subtype.ext (by
    change ((x : ℍ) + y) * z - z * ((x : ℍ) + y) = ((x : ℍ) * z - z * x) + ((y : ℍ) * z - z * y)
    noncomm_ring)
  lie_add x y z := Subtype.ext (by
    change (x : ℍ) * ((y : ℍ) + z) - ((y : ℍ) + z) * x = ((x : ℍ) * y - y * x) + ((x : ℍ) * z - z * x)
    noncomm_ring)
  lie_self x := Subtype.ext (by
    change (x : ℍ) * x - x * x = 0
    exact sub_self _)
  leibniz_lie x y z := Subtype.ext (by
    change (x : ℍ) * ((y : ℍ) * z - z * y) - ((y : ℍ) * z - z * y) * x =
      (((x : ℍ) * y - y * x) * z - z * ((x : ℍ) * y - y * x)) +
        ((y : ℍ) * ((x : ℍ) * z - z * x) - ((x : ℍ) * z - z * x) * y)
    noncomm_ring)

instance : LieBracketSMul ℝ ImH where
  lie_smul t x y := Subtype.ext (by
    change (x : ℍ) * (t • (y : ℍ)) - (t • (y : ℍ)) * x = t • ((x : ℍ) * y - y * x)
    rw [mul_smul_comm, smul_mul_assoc, smul_sub])

theorem ImH.bracket_coe (x y : ImH) : ((⁅x, y⁆ : ImH) : ℍ) = (x : ℍ) * y - y * x := rfl

/-- Dimensión de `𝔰𝔲(2)`: 3. -/
theorem finrank_ImH : Module.finrank ℝ ImH = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
  have hsurj : LinearMap.range (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    exact ⟨(r : ℍ), by simp [QuaternionAlgebra.reₗ]⟩
  have h2 : Module.finrank ℝ (LinearMap.range (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))) = 1 := by
    rw [hsurj, finrank_top]
    exact Module.finrank_self ℝ
  have h4 : Module.finrank ℝ (QuaternionAlgebra ℝ (-1) 0 (-1)) = 4 :=
    QuaternionAlgebra.finrank_eq_four (-1 : ℝ) 0 (-1)
  rw [h2, h4] at h
  exact (by omega : ∀ n : ℕ, 1 + n = 4 → n = 3) _ h

/-- Producto interior en `𝔰𝔲(2)` (restricción del de `ℍ`): `⟪x, y⟫ = (x * star y).re`. -/
theorem ImH.inner_def (x y : ImH) : (inner ℝ x y : ℝ) = ((x : ℍ) * star (y : ℍ)).re := by
  rw [Submodule.coe_inner, Quaternion.inner_def]

/-- **Invariancia del producto interior**: `⟪⁅x, y⁆, z⟫ = ⟪x, ⁅y, z⁆⟫`
(la métrica de `S³` es bi-invariante). -/
theorem ImH.inner_bracket (x y z : ImH) :
    (inner ℝ ⁅x, y⁆ z : ℝ) = inner ℝ x ⁅y, z⁆ := by
  simp only [ImH.inner_def, ImH.bracket_coe, ImH.star_coe]
  have hx := ImH.re_eq_zero x
  have hy := ImH.re_eq_zero y
  have hz := ImH.re_eq_zero z
  simp [hx, hy, hz]
  ring

/-- Identidad clave (para la simplicidad): para `u, v` puros,
`⁅v, ⁅u, v⁆⁆ = 4‖v‖² u + 4 re(u v) v`. -/
theorem ImH.bracket_bracket (u v : ImH) :
    ⁅v, ⁅u, v⁆⁆ = (4 * normSq (v : ℍ)) • u + (4 * ((u : ℍ) * v).re) • v := by
  apply Subtype.ext
  simp only [ImH.bracket_coe, Submodule.coe_add, Submodule.coe_smul]
  have hu := ImH.re_eq_zero u
  have hv := ImH.re_eq_zero v
  ext <;> simp [normSq_def', hu, hv] <;> ring

/-- **C2: `𝔰𝔲(2)` es simple** (no tiene ideales propios no triviales y no es abeliana). -/
theorem ImH.isSimple : LieAlgebra.IsSimple ℝ ImH where
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
      have hmem : (4 * normSq (v : ℍ)) • u ∈ I := by
        have h1 : ⁅v, ⁅u, v⁆⁆ ∈ I := I.lie_mem (I.lie_mem hvI)
        have h2 : (4 * ((u : ℍ) * v).re) • v ∈ I := I.smul_mem _ hvI
        have := I.sub_mem h1 h2
        rwa [ImH.bracket_bracket, add_sub_cancel_right] at this
      have hne : (4 * normSq (v : ℍ)) ≠ 0 := by
        have : (v : ℍ) ≠ 0 := fun h => hv0 (Subtype.ext h)
        have := normSq_ne_zero.mpr this
        positivity
      have := I.smul_mem (4 * normSq (v : ℍ))⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  non_abelian := by
    intro h
    -- `⁅i, j⁆ = 2k ≠ 0`
    let i : ImH := ⟨⟨0, 1, 0, 0⟩, by rw [mem_ImH]⟩
    let j : ImH := ⟨⟨0, 0, 1, 0⟩, by rw [mem_ImH]⟩
    have h0 : ⁅i, j⁆ = 0 := h.trivial i j
    have := congrArg (fun x : ImH => (x : ℍ).imK) h0
    simp [ImH.bracket_coe, i, j] at this

/-! ## C1 — Isotropía direccional: la acción adjunta -/

/-- Conjugación `v ↦ q v q⁻¹` de un cuaternión unitario sobre los cuaterniones puros
(es la acción adjunta `Ad(q)` de `S³ ≅ SU(2)` sobre `𝔰𝔲(2)`). -/
theorem conj_mem_ImH (q : ℍ) (v : ImH) : q * v * star q ∈ ImH := by
  rw [mem_ImH, ← star_eq_neg]
  simp only [star_mul, star_star, ImH.star_coe, mul_neg, neg_mul, mul_assoc]

/-- La conjugación como aplicación lineal `ImH →ₗ[ℝ] ImH`. -/
def conjL (q : ℍ) : ImH →ₗ[ℝ] ImH where
  toFun v := ⟨q * v * star q, conj_mem_ImH q v⟩
  map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' t x := Subtype.ext (by simp)

theorem conjL_apply_coe (q : ℍ) (v : ImH) : ((conjL q v : ImH) : ℍ) = q * v * star q := rfl

theorem conjL_conjL (p q : ℍ) (v : ImH) : conjL p (conjL q v) = conjL (p * q) v :=
  Subtype.ext (by simp only [conjL_apply_coe, star_mul, mul_assoc])

theorem conjL_one (v : ImH) : conjL 1 v = v := Subtype.ext (by simp [conjL_apply_coe])

/-- `Ad(q)` como isometría lineal de `𝔰𝔲(2)` (es decir, `Ad(q) ∈ O(3)`). -/
def AdS3' (q : S3) : ImH ≃ₗᵢ[ℝ] ImH :=
  { conjL q with
    invFun := conjL (star (q : ℍ))
    left_inv := fun v => by
      change conjL (star (q : ℍ)) (conjL q v) = v
      rw [conjL_conjL, star_mul_self_of_mem_S3, conjL_one]
    right_inv := fun v => by
      change conjL q (conjL (star (q : ℍ)) v) = v
      rw [conjL_conjL, self_mul_star_of_mem_S3, conjL_one]
    norm_map' := fun v => by
      change ‖conjL q v‖ = ‖v‖
      rw [← Submodule.norm_coe (conjL (q : ℍ) v), ← Submodule.norm_coe v, conjL_apply_coe,
        norm_mul, norm_mul, norm_star, mem_sphere_zero_iff_norm.1 q.2, one_mul, mul_one] }

theorem AdS3'_apply_coe (q : S3) (v : ImH) :
    ((AdS3' q v : ImH) : ℍ) = q * v * star (q : ℍ) := rfl

/-- **La acción adjunta `Ad : SU(2) ≅ S³ →* O(𝔰𝔲(2))`.** -/
def AdS3 : S3 →* (ImH ≃ₗᵢ[ℝ] ImH) where
  toFun := AdS3'
  map_one' := LinearIsometryEquiv.ext fun v => Subtype.ext (by
    simp [AdS3'_apply_coe])
  map_mul' p q := LinearIsometryEquiv.ext fun v => Subtype.ext (by
    simp only [AdS3'_apply_coe, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      Metric.unitSphere.coe_mul, star_mul, mul_assoc])

theorem AdS3_apply_coe (q : S3) (v : ImH) :
    ((AdS3 q v : ImH) : ℍ) = q * v * star (q : ℍ) := rfl

/-- `Ad(q)` es un automorfismo del álgebra de Lie: `Ad(q)⁅x, y⁆ = ⁅Ad(q) x, Ad(q) y⁆`. -/
theorem AdS3_bracket (q : S3) (x y : ImH) : AdS3 q ⁅x, y⁆ = ⁅AdS3 q x, AdS3 q y⁆ := by
  apply Subtype.ext
  simp only [AdS3_apply_coe, ImH.bracket_coe]
  have h : star (q : ℍ) * q = 1 := star_mul_self_of_mem_S3 q
  have key : ∀ a b : ℍ, (q * a * star (q : ℍ)) * (q * b * star (q : ℍ)) =
      q * (a * b) * star (q : ℍ) := by
    intro a b
    have : (q * a * star (q : ℍ)) * (q * b * star (q : ℍ)) =
        q * a * (star (q : ℍ) * q) * b * star (q : ℍ) := by
      simp only [mul_assoc]
    rw [this, h, mul_one]
    simp only [mul_assoc]
  rw [key, key, mul_sub, sub_mul]

/-! ### Identidades cuaterniónicas para la transitividad -/

/-- Para `v, w` puros: `(v + w) v (v + w)* = (‖v‖² − ‖w‖²) v + 2(‖v‖² − re(v w)) w`. -/
theorem conj_add_identity (v w : ℍ) (hv : v.re = 0) (hw : w.re = 0) :
    (v + w) * v * star (v + w) =
      (normSq v - normSq w) • v + (2 * (normSq v - (v * w).re)) • w := by
  ext <;> simp [normSq_def', hv, hw] <;> ring

/-- Para `v, w` puros: `‖v + w‖² = ‖v‖² + ‖w‖² − 2 re(v w)`. -/
theorem normSq_add_pure (v w : ℍ) (hv : v.re = 0) (hw : w.re = 0) :
    normSq (v + w) = normSq v + normSq w - 2 * (v * w).re := by
  simp [normSq_def', hv, hw]; ring

/-- Para `u, v` puros: `u v u* = −2 re(v u) u − ‖u‖² v`. -/
theorem conj_orth_identity (u v : ℍ) (hu : u.re = 0) (hv : v.re = 0) :
    u * v * star u = (-2 * (v * u).re) • u + (-normSq u) • v := by
  ext <;> simp [normSq_def', hu, hv] <;> ring

/-- Todo cuaternión puro no nulo admite un cuaternión puro no nulo ortogonal. -/
theorem exists_orthogonal_pure (v : ℍ) (hv : v.re = 0) :
    ∃ u : ℍ, u.re = 0 ∧ u ≠ 0 ∧ (v * u).re = 0 := by
  by_cases h : v.imI = 0 ∧ v.imJ = 0
  · refine ⟨⟨0, 1, 0, 0⟩, rfl, ?_, ?_⟩
    · intro h0
      have := congrArg QuaternionAlgebra.imI h0
      norm_num at this
    · simp [h.1, hv]
  · refine ⟨⟨0, -v.imJ, v.imI, 0⟩, rfl, ?_, ?_⟩
    · intro h0
      apply h
      have h1 := congrArg QuaternionAlgebra.imI h0
      have h2 := congrArg QuaternionAlgebra.imJ h0
      simp at h1 h2
      exact ⟨h2, h1⟩
    · simp [hv]; ring

/-- Normalización: si `q₀ ≠ 0` y `q₀ v q₀* = ‖q₀‖² w`, entonces el cuaternión unitario
`q = q₀ / ‖q₀‖` cumple `Ad(q) v = w`. -/
theorem AdS3_of_conj_eq (q₀ : ℍ) (hq₀ : q₀ ≠ 0) (v w : ImH)
    (h : q₀ * v * star q₀ = normSq q₀ • (w : ℍ)) :
    ∃ q : S3, AdS3 q v = w := by
  have hn : ‖q₀‖ ≠ 0 := norm_ne_zero_iff.mpr hq₀
  refine ⟨⟨‖q₀‖⁻¹ • q₀, by rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ hn]⟩, Subtype.ext ?_⟩
  show (‖q₀‖⁻¹ • q₀) * v * star (‖q₀‖⁻¹ • q₀) = (w : ℍ)
  have key : (‖q₀‖⁻¹ • q₀) * v * star (‖q₀‖⁻¹ • q₀) =
      (‖q₀‖⁻¹ * (‖q₀‖⁻¹ * normSq q₀)) • (w : ℍ) := by
    rw [Quaternion.star_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, h, smul_smul,
      smul_smul]
    congr 1
    ring
  rw [key, normSq_eq_norm_mul_self]
  have : ‖q₀‖⁻¹ * (‖q₀‖⁻¹ * (‖q₀‖ * ‖q₀‖)) = 1 := by field_simp
  rw [this, one_smul]

/-- **C1 — Isotropía direccional: la acción adjunta de `S³ ≅ SU(2)` es transitiva sobre la
esfera unidad de `𝔰𝔲(2)`.** Ninguna dirección del álgebra de Lie está privilegiada. -/
theorem AdS3_transitive (v w : ImH) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ q : S3, AdS3 q v = w := by
  have hv' : normSq (v : ℍ) = 1 := by
    rw [normSq_eq_norm_mul_self, Submodule.norm_coe, hv, one_mul]
  have hw' : normSq (w : ℍ) = 1 := by
    rw [normSq_eq_norm_mul_self, Submodule.norm_coe, hw, one_mul]
  have hvre := ImH.re_eq_zero v
  have hwre := ImH.re_eq_zero w
  by_cases hvw : (w : ℍ) = -v
  · -- caso antipodal: conjugar por un puro ortogonal a `v`
    obtain ⟨u, hu, hu0, huv⟩ := exists_orthogonal_pure v hvre
    refine AdS3_of_conj_eq u hu0 v w ?_
    rw [conj_orth_identity u v hu hvre, huv, hvw]
    simp
  · -- caso general: conjugar por `v + w`
    have hq0 : (v : ℍ) + w ≠ 0 := by
      intro h; apply hvw; rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    refine AdS3_of_conj_eq ((v : ℍ) + w) hq0 v w ?_
    rw [conj_add_identity v w hvre hwre, normSq_add_pure v w hvre hwre, hv', hw', sub_self,
      zero_smul, zero_add]
    congr 1
    ring

/-- **C1 (imagen en `O(3)`)**: cada `Ad(q)` es una isometría lineal de `𝔰𝔲(2) ≅ ℝ³`
(esto es exactamente `Ad(q) ∈ O(3)`; es parte de la construcción de `AdS3`). -/
theorem AdS3_isometry (q : S3) (v : ImH) : ‖AdS3 q v‖ = ‖v‖ := (AdS3 q).norm_map v

/-- **C1 (imagen = SO(3)): ADMITIDO.**
La imagen de `Ad` es exactamente `SO(3)`: (a) cada `Ad(q)` tiene determinante `+1`
(por conexión de `S³`, o por cálculo directo `det = ‖q‖⁶ = 1`), y (b) toda rotación
de `ℝ³` proviene de un cuaternión unitario (parametrización de Euler–Rodrigues).
Mathlib no dispone de `SO(3)` como grupo de transformaciones de `𝔰𝔲(2)` ni de la
parametrización de Euler–Rodrigues; formalizar (b) requiere construir la rotación
inversa a partir de ángulo y eje. Lo dejamos admitido; la parte que el tratado usa
realmente (transitividad sobre direcciones) está probada en `AdS3_transitive`. -/
theorem AdS3_image_eq_SO3 :
    (∀ q : S3, LinearMap.det ((AdS3 q).toLinearEquiv : ImH →ₗ[ℝ] ImH) = 1) ∧
    (∀ R : ImH ≃ₗᵢ[ℝ] ImH, LinearMap.det (R.toLinearEquiv : ImH →ₗ[ℝ] ImH) = 1 →
      ∃ q : S3, AdS3 q = R) := by
  sorry

/-! ## Bonus — `SU(2) ≅ S³`

* Como grupos topológicos: `ψTop : S3 ≃ₜ* SU2` (**probado** arriba).
* Como variedades: `S3` es una variedad analítica (**probado**, instancia
  `IsManifold (𝓡 3) ω S3`). Mathlib no dota a `Matrix.specialUnitaryGroup` de estructura
  de variedad; la estructura diferenciable de `SU2` se *define* transportando la de `S3`
  a lo largo del homeomorfismo `ψHomeo`, con lo que el difeomorfismo es tautológico. -/

/-- **Bonus: `SU(2)` es homeomorfo a `S³` y el homeomorfismo es un isomorfismo de grupos.** -/
theorem bonus_SU2_iso_S3 : Nonempty (S3 ≃ₜ* SU2) := ⟨ψTop⟩

/-! ## Resumen de la etapa 1 (véase `ETAPA1.md`) -/

/-- Enunciado-resumen: todas las propiedades probadas de la etapa 1 sobre `S³ ≅ SU(2)`. -/
theorem etapa1_resumen :
    -- C1: isotropía direccional (transitividad de Ad sobre la esfera unidad de 𝔰𝔲(2))
    (∀ v w : ImH, ‖v‖ = 1 → ‖w‖ = 1 → ∃ q : S3, AdS3 q v = w) ∧
    -- C2: 𝔰𝔲(2) simple
    LieAlgebra.IsSimple ℝ ImH ∧
    -- C3: homogeneidad
    MulAction.IsPretransitive SU2 SU2 ∧
    -- C4: compacidad
    CompactSpace SU2 ∧
    -- C5: sin orden total invariante
    (∀ r : SU2 → SU2 → Prop, ¬ IsInvariantTotalOrder r) ∧
    -- DR: P singleton, G infinito
    (Subsingleton P ∧ Infinite SU2) ∧
    -- Polaridad
    (∃ g : SU2, g ≠ g⁻¹) ∧
    -- Continuo: conexo y grupo de Lie (vía S³)
    (ConnectedSpace SU2 ∧ LieGroup (𝓡 3) ω S3) ∧
    -- Bonus
    Nonempty (S3 ≃ₜ* SU2) :=
  ⟨AdS3_transitive, ImH.isSimple, inferInstance, inferInstance, C5_SU2,
    ⟨inferInstance, inferInstance⟩, polaridad_SU2, ⟨inferInstance, inferInstance⟩,
    bonus_SU2_iso_S3⟩

end Compila
