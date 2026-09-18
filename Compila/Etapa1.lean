/-
# Etapa1.lean — Propiedades de SU(2)

Solo enunciados. TODAS las demostraciones son `sorry` (salvo las marcadas PROBADO).
Cada enunciado indica qué nociones de Mathlib usa y qué nombre pedido en el guion se
ha tenido que adaptar.
-/

import Compila.Definiciones
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

open Matrix

noncomputable section

namespace Compila

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **C1 (isotropía).** `Ad` actúa transitivamente sobre la esfera unidad de su(2).
Nociones: `Ad`, `unitSphere_su2` [PROPIO]. -/
theorem C1_isotropia :
    ∀ X ∈ unitSphere_su2, ∀ Y ∈ unitSphere_su2, ∃ g : SU2, Ad g X = Y := sorry

/-- **C2 (indivisibilidad).** su(2) es un álgebra de Lie simple (sobre ℝ).
Nombre pedido: `IsSimpleLieAlgebra su2`. Nombre real en Mathlib:
[MATHLIB: `LieAlgebra.IsSimple R L`] (`Mathlib/Algebra/Lie/Semisimple/Defs.lean`),
que es una clase `Prop` con dos campos: todo ideal es `⊥` o `⊤`, y no es abeliana. -/
theorem C2_indivisibilidad : LieAlgebra.IsSimple ℝ su2 := sorry

/-- **C3 (homogeneidad).** El grupo actúa transitivamente sobre sí mismo por traslación.
Nociones: [MATHLIB: `Group SU2`]. -/
theorem C3_homogeneidad : ∀ g h : SU2, ∃ k : SU2, k * g = h := sorry

/-- **C4 (compacidad).** SU(2) es un espacio compacto.
Nociones: [MATHLIB: `CompactSpace`], topología de subtipo de `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem C4_compacto : CompactSpace SU2 := sorry

/-- **C4' (cerrado bajo la operación).** Trivial: el producto de dos elementos de SU(2)
está en SU(2) (es la propia estructura de grupo). -/
theorem C4_cerrado : ∀ g h : SU2, g * h ∈ (Set.univ : Set SU2) := sorry

/-- **DR (singleton).** P tiene exactamente un elemento.
Nombre pedido: `theorem DR_singleton : Unique P`. ADAPTACIÓN: `Unique P` es un `Type`, no
una `Prop`, y Lean 4 rechaza un `theorem` cuyo tipo no es una proposición; se enuncia por
tanto como `Nonempty (Unique P)` (= `EsSingleton P`), que sí es `Prop`. -/
theorem DR_singleton : EsSingleton P := sorry

/-- **DR (infinitud).** SU(2) es infinito. Nociones: [MATHLIB: `Infinite`]. -/
theorem DR_infinito : Infinite SU2 := sorry

/-- **Polaridad.** Hay elementos que no son su propio inverso. -/
theorem polaridad : ∃ g : SU2, g ≠ g⁻¹ := sorry

/-- **Continuo / conexión.** SU(2) es conexo. Nociones: [MATHLIB: `ConnectedSpace`]. -/
theorem continuo_conexo : ConnectedSpace SU2 := sorry

/-- **Bonus.** SU(2) es homeomorfo a la esfera S³ ⊂ ℝ⁴.
Nociones: [MATHLIB: `Homeomorph` (notación `≃ₜ`)], [MATHLIB: `Metric.sphere`],
[MATHLIB: `EuclideanSpace ℝ (Fin 4)`]. -/
theorem bonus_S3 :
    Nonempty (SU2 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := sorry

end Compila

end
