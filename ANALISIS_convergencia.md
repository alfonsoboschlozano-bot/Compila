# Análisis del teorema `convergencia` (Etapa3.lean)

Contexto: esqueleto Lean 4 + Mathlib v4.34.0 del proyecto `Compila`. Definiciones vigentes:

```
A1_clausura G      := CompactSpace G
A2_convergencia P G := EsSingleton P ∧ Infinite G ∧ AlgebraSimple (lieAlgebra G)
A3_relieve G       := (⊤ : LieSubalgebra ℝ (lieAlgebra G)) ≠ ⊥
                     ∧ (∃ g h : G, g ≠ 1 ∧ h ≠ 1 ∧ ¬ IsConj g h)
                     ∧ CurvaturaPositivaConstante G          -- opaque, no formalizado
A4_isotropia G     := AdTransitivaEnEsfera G

C1 G := AdTransitivaEnEsfera G
C2 G := AlgebraSimple (lieAlgebra G)
C3 G := ∀ g h : G, ∃ k : G, k * g = h
C4 G := CompactSpace G ∧ ∀ g h : G, g * h ∈ Set.univ
C5 G := ∃ g : G, g ≠ g⁻¹
DR P G := EsSingleton P ∧ Infinite G
Continuo G := ConnectedSpace G

theorem convergencia (P G) [LieGroupCompactoConexo G] :
  (A1 ∧ A2 ∧ A3 ∧ A4) ↔ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ DR ∧ Continuo)
```

La clase propia `LieGroupCompactoConexo G` extiende `Group`, `TopologicalSpace`,
`IsTopologicalGroup`, `CompactSpace`, `ConnectedSpace`, y añade un álgebra de Lie real `𝔤`,
`Ad : G →* (𝔤 ≃ₗ[ℝ] 𝔤)` y una forma cuadrática `normSq : 𝔤 → ℝ` invariante por `Ad`.
La esfera es `{X | normSq X = 1}`. No exige Hausdorff ni ninguna relación entre G y `𝔤`
más allá de la existencia de `Ad`.

## Dirección → (de A1–A4 a C1–C7)

| Conclusión | De dónde sale | Tipo |
|---|---|---|
| C1 | A4, literalmente la misma proposición | desempaquetado puro |
| C2 | tercer conjunto de A2 | desempaquetado puro |
| C3 | axiomas de grupo, `k = h * g⁻¹` | trivial, no necesita hipótesis |
| C4 | A1 más `Set.mem_univ` | desempaquetado puro |
| DR | dos primeros conjuntos de A2 | desempaquetado puro |
| Continuo | `ConnectedSpace G` ya es parte de la clase | trivial, sale de la instancia |
| C5 | ninguna A lo da | contenido real, y hoy no demostrable |

Sobre C5: la clase no exige relación entre G y `𝔤` salvo la existencia de `Ad`, ni Hausdorff.
Contramodelo: un grupo abeliano infinito con todos los elementos de orden 2, topología
indiscreta (compacto y conexo), `𝔤` cualquier álgebra de Lie simple con `Ad` trivial y
`normSq = 0` (esfera vacía, así que A4 se cumple por vacuidad). Satisface A1, A2, A4 y las
dos primeras partes de A3, pero no C5.

Detalle: `A1_clausura` y la primera mitad de `C4` son redundantes, porque `CompactSpace G`
ya está dentro de la clase.

## Dirección ← (de C1–C7 a A1–A4)

| Conclusión | De dónde sale | Tipo |
|---|---|---|
| A1, A2, A4 | C4, DR con C2, C1 | desempaquetado puro |
| A3 parte 1, `⊤ ≠ ⊥` | C2: simple implica no trivial; Mathlib tiene `LieAlgebra.IsSimple.nontrivial` | contenido pequeño, un lema |
| A3 parte 2, dos elementos no conjugados | C5 no basta: `g` y `g⁻¹` pueden ser conjugados, y en SU(2) siempre lo son | contenido real, y con la clase actual falso |
| A3 parte 3, curvatura | nada | imposible mientras sea `opaque` |

Sobre la parte 2: existen grupos infinitos donde todos los elementos no triviales son
conjugados entre sí (construcciones HNN). Con topología indiscreta y el mismo truco de
esfera vacía cumplen C1–C7 y fallan A3. La implicación ← es falsa tal como está escrita la
clase, no solo difícil.

## Si se quita `CurvaturaPositivaConstante` de A3

Compila sin cambios en el resto (comprobado en un archivo de prueba con `A3_relieve'` y
`convergencia'`).

- Se gana: la dirección ← deja de tener una obligación imposible, y `convergencia` pasa a
  ser un enunciado con valor de verdad determinado.
- Se pierde: nada en cuanto a lo que el corolario quiere decir, porque la curvatura no aporta
  información formal (es una proposición opaca). Informalmente, álgebra simple más `Ad`
  transitiva en la esfera ya fuerza dimensión 3 y su(2); la curvatura positiva constante es
  consecuencia, no hipótesis independiente.

## Recomendación

Para que el ↔ sea demostrable y no vacío:

1. Quitar la curvatura de A3.
2. Añadir a la clase lo que liga G con `𝔤`: como mínimo `T2Space G`, y que `Ad` sea fiel o
   que la esfera sea no vacía.

Sin eso, ninguna de las dos direcciones con contenido real es cierta.
