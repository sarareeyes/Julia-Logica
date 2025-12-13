include("PropositionalLogic/src/PropositionalLogic.jl")
using.PropositionalLogic

# ======================= EJEMPLOS DE USO =======================
# ===============================================================

PropositionalLogic.version()

# Crear variables
# ---------------

hoy = Var_PL("hoy_llueve")
p, q, r, s = vars(:p, :q, :r, :s)

# Nota: también se pueden crear variables con vars("p", "q", "r", "s")
# ¿Qué es un símbolo?

# Algunas fórmulas de ejemplo
# ---------------------------
hoy | -hoy
(((p > q) | r) > (p & -p))
(- (p & q) > (q & r))
((p > (q & r)) > (-(-p) & q))
p ~ (q ~ (r | s))
p > q & r

# Nota: No se necesitan paréntesis para agrupar, ya que la precedencia de los operadores está definida en la librería.
# Nota: Las variables proposicionales deben estar declaradas previamente.

# Crear y mostrar fórmulas
# ------------------------
f0 = -p
f1 = p & q
f2 = p | q
f3 = p > q
# f3mal = p > | q
f4 = p ~ q
f5 = !(p & q)
f6 = -(p & q)

f7 = f1 | f2 > f3

f = -(-(p | q) > (-r & s))

vars_of(f)

# Análisis demo de fórmulas
# ------------------------
analyze(f)
compare_algorithms(f, iterations = 100)

# Mostrar subfórmulas y árbol de formación
# ----------------------------------------
f0 |> subformulas
f1 |> subformulas
f2 |> subformulas
f6 |> subformulas
f0 |> formation_tree
f1 |> formation_tree
(f6 | f2) |> formation_tree
analyze(f6 | f2)

# Valoraciones y Evaluaciones
# ---------------------------
v1 = Valuation(p => true, q => false, r => true)
v1(f0)
v1(f1)
v1(f1) == evaluate(f1, v1)  # Evaluar f1 con la valoración v1
v1(f2)                      # Evaluar f2 con la valoración v1
v1(f3)                      # Evaluar f3 con la valoración v1
v1(f4)                      # Evaluar f4 con la valoración v1
v1(f5)                      # Evaluar f5 con la valoración v1

v2 = Valuation(p => 1, q => 0, r => 1)
v2(f0)
v2(f1)
v2(f1) == evaluate(f1, v2)  # Evaluar f1 con la valoración v2
v2(f2)                      # Evaluar f2 con la valoración v2
v2(f3)                      # Evaluar f3 con la valoración v2
v2(f4)                      # Evaluar f4 con la valoración v2
v2(f5)                      # Evaluar f5 con la valoración v2

# Nota: las valoraciones pueden definirse con true/false o con 1/0

# Tabla de verdad
# ---------------

## Tablas de verdad, modelos y contra-modelos
print_table(truth_table(f1))
f1 |> truth_table |> print_table

print_table(models(f1))
f1 |> models |>  print_table

print_table(countermodels(f1))
f1 |> countermodels |> print_table

## Tabla de verdad para varias fórmulas
funcs = [f1, f2, f3, f4, f5]
for (i,f) in enumerate(funcs)
    println("F$i = $f")
end

print_table(truth_table(funcs))
funcs |> truth_table |> print_table

# Nota: La tabla de verdad para varias fórmulas puede ser interesante para comprobar consecuencias lógicas, pero debe tenerse en cuenta que el número de columnas crece rápidamente y rápidamente puede ser inmanejable.

# Tautologías, Contradicciones, Satisfacibilidad
# ----------------------------------------------
f_taut = p | -p
f_unsat = p & -p
f_sat  = p & q

for f in [f_taut, f_unsat, f_sat]
    println("Análisis de fórmula proposicional:")
    println("---------------------------------")
    println("Fórmula: $f")
    println("Variables: ", vars_of(f))
    println("Tabla de verdad:")
    print_table(truth_table(f))
    println("Modelos: ", models(f))
    println("Contra-modelos: ", countermodels(f))
    println("¿Es tautología? ", TAUT(f))
    println("¿Es contradicción? ", UNSAT(f))
    println("¿Es satisfacible? ", SAT(f))
    println()
end


# Nota: La implementación de estas funciones sigue el mismo patrón que los 
# cálculos de la tabla de verdad, por lo que son computacionalmente costosas 
# para fórmulas con muchas variables, pero usan cortocircuitos para evitar 
# cálculos innecesarios (por ejemplo, para una tautología, tan pronto como 
# se encuentra una valoración que la hace falsa, se detiene y devuelve false).

# Consecuencia lógica  (comprobación del Teorema de la Consecuencia)
# --------------------------------------------------------------------
Γ = [p > q, p]
φ = q
⋀(Γ)
⋁(Γ)

print_table(truth_table([Γ..., φ]))
print_table(truth_table(⋀(Γ) > φ))

LC_Def(Γ, φ)
LC_TAUT(Γ, φ)
LC_RA(Γ, φ)

# Equivalencia lógica
# -------------------
g1 = -(p & q)
g2 = -p | -q
EQUIV(g1, g2)
EQUIV_models(g1, g2)

# Nota: EQUIV mira si g1 ↔ g2 es una tautología, mientras que EQUIV_models compara los modelos de ambas fórmulas.

# Formas Normales
# ---------------
f7 = (p > q) & (q > r)
f7 |> to_CNF
f7 |> to_DNF

f=-(((q | r) > (p & r)) > ((r | p) > (-q & p)))
f |> to_CNF
f |> to_DNF
f |> to_CF

# Comprobemos que las formas normales son equivalentes a la fórmula original
EQUIV(f, to_CNF(f))
EQUIV(f, to_DNF(f))

# Nota: En la representación completa de las formas normales, los paréntesis pueden ser numerosos, pero la librería los reduce para que sea más legible.

# Formas Clausales
# ----------------
f = ((p ~ q) ~ (q | p))
Cl =  f |> to_CF

# Nota: La forma clausal se representa como un conjunto de cláusulas. Es importante tener en cuenta que la forma clausal no es una fórmula en el sentido tradicional, sino una representación especial que facilita ciertos algoritmos (como DPLL y Resolución). Por lo que hay ciertas operaciones que no se pueden realizar directamente sobre ella, como evaluar su valor con una valoración.

# Algoritmo DPLL
# --------------

# Propagación de unidades
apply_val(Cl, p, true)
apply_val(Cl, p, false)

# Cálculo de Satisfactibilidad
f = (p | q) & (-p | r) & (-q | -r)
cl = f |> to_CF

# Nota: Por defecto, DPLL(f) = DPLL(f, verbose=false)
DPLL(cl)
cl |> DPLL
DPLL(cl; verbose=true)
# Nota: DPLL funciona sobre formas clausales,... en principio no sobre fórmulas generales.

# Pero es fácil definir una función que trabaje sobre fórmulas (basta encadenar una conversión con una llamada a la función que trabaja sobre formas clausales):
DPLL(f, verbose=true)
DPLL(f)

# Fórmula insatisfacible
formula_unsat = (p > q) & p & -q 
DPLL(formula_unsat, verbose=true)
DPLL(formula_unsat)

# Fórmula más compleja
f8 = (p | q | r) & (-p | -q) & (-p | -r) & (-q | -r) 
DPLL(f8, verbose=true)
DPLL(f8)

# Usar notación de función parcial para activar el modo verbose
verbose(f) = x -> f(x, verbose = true)
f8 |> (DPLL |> verbose)


# Comparación con método de tabla de verdad
f9 = (p | q) & (-p | r) & (q | -r)
DPLL(f9)
SAT(f9)

# Podemos aplicar DPLL al análisis de la consecuencia lógica usando el teorema fundamental del tema 1 (por reducción al absurdo, pero la función DPLL_LC se encarga de prepararlo a partir de las premisas y la conclusión):
Γ = [
    p > q,          # p → q
    q > r,          # q → r
    p               # p 
]

φ = r      # Por tanto r

DPLL(⋀([Γ..., -φ]))
# Verificador de consecuencia lógica por DPLL:
DPLL_LC(Γ, φ)

# Tableros Semánticos
# ===================
p, q, r, s = vars(:p, :q, :r, :s)

# Visualización de tableros semánticos
# ------------------------------------
# Cargar Plots.jl
using Plots

formula = (p>(-q|r))&(-q>r)&(-(p>r))

# OPCIÓN 1: Uso abreviado: terminal y gráfico
formula |> TS |> print_TS
formula |> TS |> plot_TS

# OPCIÓN 2: Extraer el nodo manualmente
f_bis2 = (p>(-q|r))&(-q>r)&(-(p>r))
f_bis2 |> TS |> print_TS
f_bis2 |> TS |> plot_TS
# Uso personalizado:
plot_TS(f_bis2 |> TS, title="Tablero Semántico de\n $f_bis2")

# Utilidades basadas en TS
# ------------------------
f10 = (p>(-q|r))&(-q>r)&(-(p>r))
f10 |> TS_SAT

# Tautología
f_taut = p | -p
f_taut |> TS_TAUT

# Contradicción
f_contr = p & -p
f_contr |> TS_SAT

# Conjunto de fórmulas
fs=[p > q, (-s & r) > q, -q, q ~ (r & s)]
fs |> TS
t_fs, m_fs = TS(fs)
ms = [⋀(m["literals"]) for m in m_fs]
⋁(ms)

# Tablero de F y de -F: FND y FNC
f_bis = (p & q) ~ (-p | r)
f_bis |> DNF_from_TS
f_bis |> to_DNF
f_bis |> CNF_from_TS
f_bis |> to_CNF
EQUIV(DNF_from_TS(f_bis), f_bis)

# Fórmula compleja
f11 = (p > q) & (q > r) & p & -r
f11 |> TS |> print_TS
f11 |> TS |> plot_TS
t11, m11 = TS(f11)
[⋀(m["literals"]) for m in m11]
TS_solve(f11)


# ========================= Resolución ========================

p, q, r, s = vars(:p, :q, :r, :s)

f = ((q | r) > (p & r)) > ((r | p) > (-q & p))
# = (p | q) & (-p) & (-q)

# Resolución solo trabaja sobre formas clausales, concretamente, conjuntos de cláusulas:
cf = f |> to_CF |> Set
resolution_saturacion(cf;verbose=true)
resolution_regular_auto(cf; verbose=true)

# Ejemplo 1: Problema insatisfacible
c1 = (p | q)  & (-p | r) & (-q | r) & -r |> to_CF |> Set
resolution_regular_auto(c1, verbose=true)

# Ejemplo 2: Con orden específico
resolution_regular(c1, [r, q, p], verbose=true)

# Ejemplo 3: Problema satisfacible
c2 = (p | q)  & (-p | r) |> to_CF |> Set
resolution_regular_auto(c2, verbose=true)

# Ejemplo 4: Comparar todos los métodos
compare_all_resolution_methods(c1, verbose=false)

# Estrategias de selección de cláusulas
# -------------------------------------

list_strategies()

c3 = p & (p | q) & ( -q | r) & -r |> to_CF |> Set 

resolution_with_strategy(c3, PositiveStrategy(), verbose=true)

# Ejemplo: Comparar todas las estrategias
compare_strategies(c3, verbose=true)

# Ejemplo: Problema con muchas cláusulas negativas
c4 = (-p | -q) & (-q | -r) & (-r | -s) & (p) & (s) |> to_CF |> Set
compare_strategies(c4, verbose=true)

# Comparación de métodos
# ======================
f15 = (p | q) & (-p | r)
println("Fórmula de prueba: $f15")
println("Tabla de verdad: $(SAT(f15))")
println("DPLL: $(DPLL(f15))")
println("Tableros semánticos: $(TS_SAT(f15))")
println("Resolución: $(resolution_saturacion(Set(to_CF(f15))))")
println("Resolución: $(resolution_regular_auto(Set(to_CF(f15))))")


# ======================= FORMALIZACIÓN DE ARGUMENTOS =======================
# ===========================================================================

#=

Formaliza en el lenguaje de la Lógica Proposicional y comprueba la validez de la
 siguiente argumentación:

"Si continúa la investigación, surgirán nuevas evidencias. 
Si surgen nuevas evidencias, entonces varios dirigentes se verán implicados. 
Si varios dirigentes están implicados, los periódicos dejarán de hablar del caso. 
Si la continuación de la investigación implica que los periódicos dejen de hablar
del caso, entonces, el surgimiento de nuevas evidencias implica que la 
investigación continúa. 
La investigación no continúa. Por tanto, no surgirán nuevas evidencias."

Siguiendo una elección similar a la del ejemplo anterior, podríamos llegar 
a la conclusión tomando como variables proposicionales:

    p : Continúa la investigación

    q : Surgen nuevas evidencias

    r : Varios dirigentes se verán implicados

    s : Los periódicos dejarán de hablar del caso.

De donde podríamos sacar las premisas siguientes:

{ p → q , q → r , r → s , (p → s) → (q → p) , ¬p }

y la conclusión: ¬q

El problema se traduce en:

¿ { p → q , q → r , r → s , (p → s) → (q → p) , ¬p } ⊧ ¬q ?
=#

p, q, r, s = vars(:p, :q, :r, :s)

premisas = [
    p > q, 
    q > r,
    r > s,
    (p > s) > (q > p),
    -p
]

conclusion = -q
println("\n=== Análisis de validez del argumento ===")
is_valid = DPLL_LC(premisas, conclusion)
println("¿Es el argumento válido? $is_valid")