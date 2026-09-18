/-
# Etapa2.lean — Unicidad

Se define una clase propia `LieGroupCompactoConexo` que empaqueta lo mínimo que hace falta
para ENUNCIAR los resultados sobre un grupo de Lie genérico G, y se enuncia el teorema de
unicidad. Todas las demostraciones son `sorry`.

## Por qué una clase propia y no `LieGroup` de Mathlib

Mathlib SÍ tiene grupos de Lie: [MATHLIB: `LieGroup I n G`] en
`Mathlib/Geometry/Manifold/Algebra/LieGroup.lean`, definida sobre una `ChartedSpace H G` con
modelo con esquinas `I : ModelWithCorners 𝕜 E H`. Pero:
  1. Mathlib NO construye el álgebra de Lie de un `LieGroup` (no existe `LieGroup.lieAlgebra`),
     ni la representación adjunta `Ad`, ni una métrica bi-invariante.
  2. `SU2` (subtipo de matrices) no tiene instancia `ChartedSpace` en Mathlib, así que ni
     siquiera podríamos instanciar `LieGroup` para nuestro ejemplo principal.
Por ello definimos una clase mínima [PROPIO] que registra solo los datos que los enunciados
necesitan: grupo topológico Hausdorff, compacto y conexo, un álgebra de Lie real `𝔤`, la
acción adjunta `Ad : G →* Aut(𝔤)` FIEL (inyectiva) y una forma cuadrática `Ad`-invariante
`normSq` (el papel de `−Killing` o de Frobenius) con la que hablar de "la esfera unidad".
Hausdorff y la fidelidad de `Ad` son lo que liga `G` con `𝔤`; sin ellas el teorema
`convergencia` de Etapa3 tiene contramodelos triviales (topología indiscreta, `Ad` trivial).
-/

import Compila.Definiciones
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

noncomputable section

namespace Compila

/-- [PROPIO] Grupo de Lie compacto y conexo "mínimo": los datos necesarios para enunciar.

Partes de Mathlib que reutiliza: [MATHLIB: `Group`], [MATHLIB: `TopologicalSpace`],
[MATHLIB: `IsTopologicalGroup`], [MATHLIB: `T2Space`], [MATHLIB: `CompactSpace`],
[MATHLIB: `ConnectedSpace`], [MATHLIB: `Function.Injective`],
[MATHLIB: `LieRing`], [MATHLIB: `LieAlgebra ℝ`], [MATHLIB: `LinearEquiv` (`≃ₗ[ℝ]`)] con su
estructura de grupo [MATHLIB: `LinearEquiv.automorphismGroup`], [MATHLIB: `MonoidHom` (`→*`)]. -/
class LieGroupCompactoConexo (G : Type*) extends
    Group G, TopologicalSpace G, IsTopologicalGroup G, T2Space G, CompactSpace G,
    ConnectedSpace G where
  /-- El álgebra de Lie (real) de `G`. -/
  𝔤 : Type
  [instLieRing : LieRing 𝔤]
  [instLieAlgebra : LieAlgebra ℝ 𝔤]
  /-- Representación adjunta: homomorfismo de grupos `G →* Aut_ℝ(𝔤)`. -/
  Ad : G →* (𝔤 ≃ₗ[ℝ] 𝔤)
  /-- `Ad` es fiel (inyectiva): es lo que hace que `𝔤` sea "el" álgebra de Lie de `G`. -/
  Ad_injective : Function.Injective Ad
  /-- Cuadrado de una norma `Ad`-invariante sobre `𝔤` (p. ej. `−Killing` o Frobenius). -/
  normSq : 𝔤 → ℝ
  /-- Invariancia de la norma bajo `Ad`. -/
  normSq_Ad : ∀ (g : G) (X : 𝔤), normSq (Ad g X) = normSq X

attribute [instance_reducible, instance] LieGroupCompactoConexo.instLieRing
  LieGroupCompactoConexo.instLieAlgebra

/-- `lieAlgebra G` : el álgebra de Lie de `G` (campo `𝔤` de la clase). [PROPIO] -/
abbrev lieAlgebra (G : Type*) [LieGroupCompactoConexo G] : Type :=
  LieGroupCompactoConexo.𝔤 (G := G)

/-- La esfera unidad de `lieAlgebra G` respecto a `normSq`. [PROPIO] -/
def esfera (G : Type*) [LieGroupCompactoConexo G] : Set (lieAlgebra G) :=
  {X | LieGroupCompactoConexo.normSq (G := G) X = 1}

/-- `AlgebraSimple L` : `L` es un álgebra de Lie real simple.
Es exactamente [MATHLIB: `LieAlgebra.IsSimple ℝ L`]; se le da nombre propio solo por
seguir la nomenclatura del guion. -/
abbrev AlgebraSimple (L : Type*) [LieRing L] [LieAlgebra ℝ L] : Prop :=
  LieAlgebra.IsSimple ℝ L

/-- `AdTransitivaEnEsfera G` : `Ad` actúa transitivamente en la esfera unidad de `lieAlgebra G`.
[PROPIO] -/
def AdTransitivaEnEsfera (G : Type*) [LieGroupCompactoConexo G] : Prop :=
  ∀ X ∈ esfera G, ∀ Y ∈ esfera G, ∃ g : G, LieGroupCompactoConexo.Ad g X = Y

/-- `EsFormaFundamental G` : álgebra de Lie simple y `Ad` transitiva en la esfera. [PROPIO] -/
def EsFormaFundamental (G : Type*) [LieGroupCompactoConexo G] : Prop :=
  AlgebraSimple (lieAlgebra G) ∧ AdTransitivaEnEsfera G

/-- `SO3` : el grupo especial ortogonal de orden 3 sobre ℝ, como tipo.

[MATHLIB: `Matrix.specialOrthogonalGroup n R : Submonoid (Matrix n n R)`]
(`Mathlib/LinearAlgebra/UnitaryGroup.lean`), que Mathlib define como
`Matrix.specialUnitaryGroup n R` con la estrella trivial `starRingOfComm`. -/
abbrev SO3 : Type := Matrix.specialOrthogonalGroup (Fin 3) ℝ

example : Group SO3 := inferInstance

/-- **Unicidad.** Un grupo de Lie compacto y conexo que es "forma fundamental" es isomorfo
(como grupo) a SU(2) o a SO(3).
Nociones: [MATHLIB: `MulEquiv` (`≃*`)], [MATHLIB: `Nonempty`]. -/
theorem unicidad (G : Type*) [LieGroupCompactoConexo G] (h : EsFormaFundamental G) :
    Nonempty (G ≃* SU2) ∨ Nonempty (G ≃* SO3) := sorry

end Compila

end
