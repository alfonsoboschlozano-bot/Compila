# INFORME — Verificación formal en Lean 4 de la estructura `F = (P, G)`

## Qué se ha hecho

Se ha construido un proyecto Lean 4 (versión 4.34.0, con la biblioteca Mathlib fijada a
la misma versión) que compila completo y contiene tres ficheros, uno por etapa:

* `Compila/Etapa1.lean` — **existencia**: el objeto `({∗}, SU(2))` existe y cumple las
  propiedades pedidas.
* `Compila/Etapa2.lean` — **unicidad**: el teorema de clasificación.
* `Compila/Etapa3.lean` — **convergencia**: las cuatro exigencias equivalen a las siete
  propiedades, y el corolario.

Compilar es ejecutar `lake build` en la raíz del proyecto (véase `README.md`). Lean
comprueba mecánicamente cada demostración; lo que compila sin `sorry` está probado.

Una nota práctica: en el entorno de trabajo los servidores de caché de Mathlib estaban
bloqueados por la red, así que hubo que compilar desde el código fuente la parte de
Mathlib que el proyecto usa (unos 2 700 módulos). No afecta al resultado.

## Cuántos enunciados hay y cuántos están probados

| | Etapa 1 | Etapa 2 | Etapa 3 | Total |
|---|---|---|---|---|
| Teoremas y lemas enunciados | 60 | 21 | 22 | **103** |
| Instancias (hechos estructurales: compacto, conexo, grupo de Lie, infinito, …) | 17 | 4 | 1 | 22 |
| Definiciones | 16 | 12 | 15 | 43 |
| Probados sin `sorry` | 59 | 21 | 22 | **102** |
| Admitidos con `sorry` | 1 | 0 | 0 | **1** |
| Axiomas con nombre | 0 | 4 | 0 | **4** |

Los 4 «axiomas» de la etapa 2 son tres resultados matemáticos clásicos que Mathlib aún
no contiene, más una noción primitiva (la dimensión del grupo `Ad(G)`):

1. `montgomery_samelson_borel` — la clasificación de Montgomery–Samelson–Borel (años 40)
   de los grupos compactos conexos que actúan transitivamente sobre esferas, en forma de
   tabla de dimensiones.
2. `adImageDim_eq_of_isSimple` (con la noción primitiva `adImageDim`) — el grupo `Ad(G)`
   tiene la misma dimensión que el álgebra de Lie cuando ésta es simple.
3. `lie_group_of_su2` — un grupo de Lie compacto y conexo cuya álgebra de Lie es `𝔰𝔲(2)`
   es `SU(2)` o `SO(3)` (teoremas de Lie y recubridor universal).

El único `sorry` está en la etapa 1: que la imagen de la acción adjunta sea
*exactamente* `SO(3)` (todo giro del espacio proviene de una lectura). Está probado que
cada `Ad(g)` es una isometría del álgebra de Lie y que la acción es transitiva sobre las
direcciones, que es lo que el tratado utiliza; falta la sobreyectividad, que exige la
parametrización de Euler–Rodrigues de las rotaciones, no disponible en Mathlib.

Un matiz de honestidad adicional: Mathlib no define la curvatura seccional ni la
acción adjunta de un grupo de Lie abstracto. Por eso (a) en las etapas 2 y 3 el «grupo
de Lie con su álgebra de Lie y su acción adjunta» es una interfaz abstracta
(`LieStructure`) en la que el álgebra de Lie, el producto interior invariante y `Ad`
son datos con los axiomas que se necesitan; y (b) la «curvatura seccional constante
positiva» se define mediante la fórmula clásica de las métricas bi-invariantes
(`K = ¼‖⁅x,y⁆‖²/(‖x‖²‖y‖²−⟪x,y⟫²)`), es decir, a nivel del álgebra de Lie. Ambas
elecciones están documentadas en `ETAPA2.md` y `ETAPA3.md`.

## Qué significa para las tres afirmaciones del tratado

**1. «Existe un objeto así» — verificado.** El objeto `({∗}, SU(2))` está construido en
Lean de dos formas (matrices y cuaterniones unitarios `S³`), demostradas isomorfas como
grupos topológicos. Se han probado, sin ningún axioma adicional ni `sorry`: la
transitividad de la acción adjunta sobre las direcciones (C1), la simplicidad del
álgebra de Lie `𝔰𝔲(2)` (C2), la homogeneidad (C3), la compacidad y clausura (C4), la
ausencia de todo orden total compatible con la operación (C5, formalizada así), el
doble registro (un solo punto, infinitas lecturas), la polaridad (`i ≠ i⁻¹`), la
conexión, la estructura de grupo de Lie de `S³`, y el isomorfismo `SU(2) ≅ S³`. Además
la estructura cumple las cuatro exigencias A1–A4 de la etapa 3 (`S3Structure_A`),
también sin axiomas. Sólo queda admitida la igualdad exacta «imagen de `Ad` = `SO(3)`».

**2. «Es único en su clase» — verificado módulo tres resultados clásicos admitidos.**
El teorema de clasificación (`clasificacion`) está demostrado en Lean a partir de los
tres axiomas nombrados. Lo que Lean verifica por sí mismo es todo lo demás: la
aritmética que, a partir de la tabla de Montgomery–Samelson–Borel, fuerza que la
dimensión sea 3 (`msb_arith`), y —el paso con más contenido— que toda álgebra de Lie
real de dimensión 3, no abeliana y con producto interior invariante es `𝔰𝔲(2) ≅ (ℝ³, ×)`
(`exists_lieEquiv_su2Model`, sin axiomas). La conclusión «`G` es `SU(2)` o `SO(3)`»
depende del axioma 3. Es importante decirlo claro: la unicidad **no** es un hecho
verificado desde cero; es un hecho verificado *dado* que se aceptan tres teoremas de la
literatura que Mathlib todavía no tiene.

**3. «Las cuatro exigencias lo requieren» — verificado módulo los mismos tres axiomas.**
La equivalencia `(A1 ∧ A2 ∧ A3 ∧ A4) ↔ (C1 ∧ … ∧ Continuo)` está probada en ambas
direcciones sin `sorry`. La mayor parte es desempaquetado de definiciones; el contenido
real está en A3 (la curvatura constante positiva y la existencia de lecturas de distinta
«magnitud») y en C5, que se obtienen de la clasificación. El corolario —toda estructura
que cumple A1–A4 es `SU(2)` o `SO(3)`— también está probado, con las mismas
dependencias. Conviene notar que con las definiciones elegidas A3 resulta *consecuencia*
de las otras tres exigencias (vía la clasificación): la geometría del «relieve» no añade
restricciones a la estructura, la describe.

En resumen: el «existe» está verificado mecánicamente casi por completo; el «es único»
y el «las cuatro lo exigen» están verificados mecánicamente en su lógica y en su
álgebra, apoyados en tres teoremas clásicos que se admiten explícitamente, con nombre,
y sin ocultar nada.

## Resumen de tres líneas

1. Existencia: `({∗}, SU(2) ≅ S³)` construido y todas sus propiedades probadas en Lean sin axiomas extra (un solo `sorry`: imagen de `Ad` exactamente `SO(3)`).
2. Unicidad: clasificación probada módulo tres resultados clásicos admitidos con nombre (MSB, dimensión de `Ad(G)`, teoremas de Lie); la dimensión 3 y `𝔤 ≅ 𝔰𝔲(2)` los verifica Lean.
3. Convergencia: `A1–A4 ↔ C1–C5, DR, Continuo` y el corolario `G ≅ SU(2)` o `SO(3)`, probados en ambas direcciones sin `sorry`, con las mismas tres dependencias.
