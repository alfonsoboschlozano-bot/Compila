# ETAPA 1 — EXISTENCIA (`Compila/Etapa1.lean`)

Objeto: `F = (P, G)` con `P = {∗}` (`Unit`) y `G = SU(2)`.

`SU(2)` se modela de dos formas, demostradas isomorfas como grupos topológicos:

* `SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ` (matrices, definición estándar de Mathlib);
* `S3 := Metric.sphere (0 : ℍ) 1` (cuaterniones unitarios).

El isomorfismo `ψTop : S3 ≃ₜ* SU2` (`q = a + bi + cj + dk ↦ [[a+bi, c+di], [−c+di, a−bi]]`)
está **probado** (homomorfismo, inyectivo, sobreyectivo, continuo, con inversa continua).
El álgebra de Lie `𝔰𝔲(2)` se modela como los cuaterniones puros `ImH` (parte real nula)
con el corchete conmutador `⁅x, y⁆ = xy − yx`; se prueba `dim ImH = 3` (`finrank_ImH`).

Estados: **PROBADO** = sin `sorry` ni axiomas; **ADMITIDO** = `sorry` con explicación;
**TRIVIAL** = consecuencia inmediata de las definiciones (también probado en Lean).

| Propiedad | Estado | Declaración Lean | Comentario |
|---|---|---|---|
| **C1** Isotropía direccional — `Ad` transitiva sobre la esfera unidad de `𝔰𝔲(2)` | **PROBADO** | `AdS3_transitive` | `Ad(q) v = q v q⁻¹`. Para `v, w` unitarios puros, `q = v + w` (si `w ≠ −v`) o `q = u ⊥ v` (si `w = −v`) lleva `v` a `w`; se normaliza `q`. Identidades cuaterniónicas `conj_add_identity`, `conj_orth_identity`, `normSq_add_pure`. |
| **C1** `Ad(q) ∈ O(3)` (isometría lineal de `𝔰𝔲(2)`) y `Ad` homomorfismo que respeta el corchete | **PROBADO** | `AdS3 : S3 →* (ImH ≃ₗᵢ[ℝ] ImH)`, `AdS3_isometry`, `AdS3_bracket` | Construcción explícita. |
| **C1** Imagen de `Ad` **exactamente** `SO(3)` | **ADMITIDO** (`sorry`) | `AdS3_image_eq_SO3` | Requiere (a) `det Ad(q) = +1` y (b) que toda rotación provenga de un cuaternión (Euler–Rodrigues). Mathlib no tiene `SO(3)` actuando sobre `𝔰𝔲(2)` ni esa parametrización; (b) exige construir eje y ángulo de una rotación arbitraria. La parte que el tratado usa (transitividad sobre direcciones) está probada. |
| **C2** Indivisibilidad — `𝔰𝔲(2)` simple | **PROBADO** | `ImH.isSimple : LieAlgebra.IsSimple ℝ ImH` | Todo ideal `I ≠ 0` contiene `v ≠ 0`; la identidad `⁅v, ⁅u, v⁆⁆ = 4‖v‖² u + 4 re(uv) v` (`ImH.bracket_bracket`) fuerza `u ∈ I` para todo `u`. No abeliana: `⁅i, j⁆ = 2k`. (En la etapa 2 se prueba además `su2Model.isSimple` para `(ℝ³, ×)`.) |
| **C3** Homogeneidad — `G` actúa transitivamente sobre sí mismo | **TRIVIAL** | `instance : MulAction.IsPretransitive SU2 SU2` | `x ↦ (y x⁻¹) x`. |
| **C4** Autosuficiencia — `G` compacto | **PROBADO** | `instance : CompactSpace SU2`, `isCompact_SU2`, `instance : CompactSpace S3` | Dos pruebas: transporte desde `S³` (esfera de un espacio propio) y directa (cerrado y acotado en `ℂ⁴`, usando `entry_norm_bound_of_unitary`). |
| **C4** Autosuficiencia — cerrado bajo la operación | **TRIVIAL** | `C4_closed_under_mul` | `G` es un grupo. |
| **C5** Atemporalidad — ningún orden total distinguido | **ENUNCIADO y PROBADO** (en la formalización elegida) | `IsInvariantTotalOrder`, `no_invariant_order_of_involution`, `C5_SU2`, `C5_S3` | Se formaliza como: **ningún** orden total estricto sobre `G` es invariante por la operación del grupo. Se prueba porque `−1 ∈ G` es una involución no trivial y un grupo con torsión no admite órdenes invariantes. |
| **DR** Doble registro — `P` singleton | **TRIVIAL** | `DR_P_subsingleton` | `P = Unit`. |
| **DR** Doble registro — `G` infinito | **PROBADO** | `instance : Infinite S3`, `instance : Infinite SU2` | Curva inyectiva `t ↦ t + √(1−t²) i` desde `[−1, 1]`. |
| **Polaridad** — existe `g ≠ g⁻¹` | **PROBADO** | `polaridad_SU2`, `polaridad_S3` | `g = i` (`i⁻¹ = −i`). |
| **Continuo** — `G` conexo | **PROBADO** | `instance : ConnectedSpace SU2`, `instance : ConnectedSpace S3` | Esfera de un espacio de dimensión `> 1`; transporte por el homeomorfismo. |
| **Continuo** — `G` variedad diferenciable / grupo de Lie | **PROBADO** (para `S³`) | `instance : IsManifold (𝓡 3) ω S3`, `instance : LieGroup (𝓡 3) ω S3` | Cartas estereográficas de Mathlib; multiplicación e inversión (`= star`, lineal) analíticas. *Matiz:* Mathlib no dota al grupo de matrices `SU2` de estructura de variedad; la suya se **define** transportando la de `S3` por `ψHomeo`, y no se ha construido aparte en Lean. |
| **Bonus** — `SU(2) ≅ S³` | **PROBADO** (como grupos topológicos) | `ψTop : S3 ≃ₜ* SU2`, `bonus_SU2_iso_S3` | Como variedades: `S3` es variedad analítica y la estructura de `SU2` es la transportada, luego el difeomorfismo es tautológico (no hay un enunciado Lean separado). |

Resumen mecánico: `etapa1_resumen` reúne todas las propiedades probadas en un solo
enunciado; `#print axioms` muestra que sólo depende de `propext`, `Classical.choice` y
`Quot.sound` (los axiomas estándar de Mathlib). El único `sorry` de la etapa es
`AdS3_image_eq_SO3`.

Nota técnica: para combinar `LieRing` con `NormedAddCommGroup`/`InnerProductSpace` sobre
el mismo tipo sin «diamante» de instancias, se introduce la clase `LieBracketOn` (corchete
sobre un grupo abeliano dado) de la que se derivan `LieRing` y `LieAlgebra` de Mathlib.
