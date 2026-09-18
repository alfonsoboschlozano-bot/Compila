/-
# Definiciones.lean

Objetos básicos de la estructura F = (P, G) con G = SU(2).

Convención de anotación en cada definición:
  * `[MATHLIB: nombre.exacto]`  — el objeto existe en Mathlib con ese nombre y se reutiliza.
  * `[PROPIO]`                  — definición mínima nuestra, porque Mathlib no la tiene tal cual.

Todas las obligaciones de prueba que aparecen dentro de definiciones son `sorry`
(el objetivo de esta sesión es que el esqueleto compile, no probar nada).
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Complex.Basic

open Matrix

noncomputable section

namespace Compila

/-! ## 1. El grupo SU(2) -/

/-- `SU2` : el grupo especial unitario de orden 2 sobre ℂ, como tipo (subtipo de las
matrices 2×2 complejas).

[MATHLIB: `Matrix.specialUnitaryGroup n α : Submonoid (Matrix n n α)`],
fichero `Mathlib/LinearAlgebra/UnitaryGroup.lean`. Mathlib ya proporciona
`Group (Matrix.specialUnitaryGroup n α)` y, por ser un subtipo de `Matrix (Fin 2) (Fin 2) ℂ`,
hereda la topología producto de `Mathlib/Topology/Instances/Matrix.lean`. -/
abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) (ℂ)

/-- Comprobaciones de que Mathlib da las instancias que necesitaremos. -/
example : Group SU2 := inferInstance
example : TopologicalSpace SU2 := inferInstance

/-! ## 2. El álgebra de Lie su(2) -/

/-- Estructura de anillo de Lie sobre las matrices dada por el conmutador `⁅X, Y⁆ = X*Y - Y*X`.

[MATHLIB: `LieRing.ofAssociativeRing`], fichero `Mathlib/Algebra/Lie/OfAssociative.lean`.
Mathlib NO la declara como instancia global (para no interferir con otras estructuras de
corchete); en Mathlib se activa localmente con exactamente esta línea
(p. ej. en `Mathlib/Algebra/Lie/Matrix.lean`). Hacemos lo mismo. -/
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Con la instancia anterior, Mathlib da `LieAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ)`
vía [MATHLIB: `LieAlgebra.ofAssociativeAlgebra`]. -/
example : LieAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

/-- `su2` : el álgebra de Lie real de SU(2): matrices 2×2 complejas antihermitianas
(`Xᴴ = -X`) y de traza cero, como subálgebra de Lie REAL de `Matrix (Fin 2) (Fin 2) ℂ`.

[PROPIO] Mathlib no tiene `su(n)` con nombre. Se construye con
[MATHLIB: `LieSubalgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ)`] (`Mathlib/Algebra/Lie/Subalgebra.lean`),
[MATHLIB: `Matrix.conjTranspose` (notación `ᴴ`)] y [MATHLIB: `Matrix.trace`].
Las cuatro obligaciones de cierre (suma, cero, escalar real, corchete) quedan como `sorry`. -/
def su2 : LieSubalgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {X | Xᴴ = -X ∧ Matrix.trace X = 0}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry
  lie_mem' := sorry

/-- `su2` es, en particular, un álgebra de Lie real (instancias que Mathlib da a cualquier
`LieSubalgebra`). -/
example : LieRing su2 := inferInstance
example : LieAlgebra ℝ su2 := inferInstance

/-! ## 3. La acción adjunta -/

/-- `Ad g X = g * X * g⁻¹` : acción adjunta de SU(2) sobre su(2) por conjugación.

[PROPIO] Mathlib tiene la acción adjunta de un álgebra de Lie sobre sí misma
(`LieAlgebra.ad`), pero no la de un grupo matricial sobre su álgebra de Lie.
`g⁻¹` es el inverso en el grupo `SU2` (que Mathlib define como `star g`, es decir `gᴴ`).
La prueba de que el resultado sigue en `su2` queda como `sorry`. -/
def Ad (g : SU2) (X : su2) : su2 :=
  ⟨(g : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) * ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ),
   sorry⟩

/-! ## 4. La esfera unidad de su(2) -/

/-- Cuadrado de la norma de Frobenius de una matriz compleja: `‖X‖² = Re tr (X * Xᴴ)`
(`= Σ |X i j|²`).

[PROPIO] Elegimos la norma de FROBENIUS (no la de Killing). Mathlib tiene la norma de
Frobenius (`Matrix.frobeniusNormedAddCommGroup`), pero solo como instancia LOCAL, no global,
así que definimos el cuadrado de la norma directamente con [MATHLIB: `Matrix.trace`],
[MATHLIB: `Matrix.conjTranspose`] y [MATHLIB: `Complex.re`]. -/
def frobNormSq (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (X * Xᴴ)).re

/-- `unitSphere_su2` : elementos de `su2` de norma de Frobenius 1.

[PROPIO] Conjunto (`Set su2`) definido a partir de `frobNormSq`. -/
def unitSphere_su2 : Set su2 :=
  {X | frobNormSq (X : Matrix (Fin 2) (Fin 2) ℂ) = 1}

/-! ## 5. El tipo P con un solo elemento -/

/-- `P` : el tipo de "puntos" de la estructura F = (P, G). Tiene un solo elemento.

[MATHLIB: `Unit`] (tipo con un único habitante `()`), y el predicado "tener exactamente un
elemento" es [MATHLIB: `Unique`] (clase = `Inhabited` + `Subsingleton`). -/
abbrev P : Type := Unit

/-- El predicado "tipo con un solo elemento".

[MATHLIB: `Unique α`]. Lo damos con nombre propio solo para seguir la nomenclatura del
enunciado; es literalmente `Unique`. -/
abbrev EsSingleton (α : Type*) : Prop := Nonempty (Unique α)

example : Unique P := inferInstance

end Compila

end
