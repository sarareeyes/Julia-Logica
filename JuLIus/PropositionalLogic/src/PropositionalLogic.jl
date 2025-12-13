"""
# PropositionalLogic - Módulo Principal de Lógica Proposicional

Este es el módulo principal que unifica toda la funcionalidad de Lógica 
Proposicional desarrollada de forma modular. Incluye tipos básicos, evaluación, 
análisis semántico y algoritmos de decisión.

## Estructura modular:

### Core (Funcionalidad básica):
- **Types**: Jerarquía de tipos y operadores lógicos
- **Evaluation**: Sistema de evaluación y valoraciones  
- **Display**: Visualización y formato de fórmulas

### Analysis (Análisis semántico):
- **TruthTables**: Generación de tablas de verdad y búsqueda de modelos
- **Properties**: Propiedades semánticas (TAUT, SAT, equivalencias)
- **NormalForms**: Transformaciones CNF/DNF y estructuras auxiliares

### Algorithms (Algoritmos de decisión):
- **DPLL**: Algoritmo Davis-Putnam-Logemann-Loveland
- **Tableaux**: Tableros semánticos (método analítico)
- **Resolution**: Algoritmo de resolución

## Características principales:
- **Educativo**: Diseñado para la enseñanza de lógica computacional
- **Completo**: Implementa los algoritmos fundamentales
- **Documentado**: Cada función incluye documentación detallada
- **Modular**: Estructura clara y extensible
- **Eficiente**: Optimizaciones para casos reales

## Uso típico:
```julia
using PropositionalLogic

# Crear variables
p, q, r = vars("p", "q", "r")

# Construir fórmulas
formula = (p > q) & (q > r) & p     # (p → q) ∧ (q → r) ∧ p

# Análisis básico
TAUT(formula)  # false
SAT(formula)   # true

# Algoritmos avanzados
DPLL(formula)
TS(formula)
resolution_regular(formula)
```
"""
module PropositionalLogic

# ==================== INCLUSIÓN DE SUBMÓDULOS ====================

# Core modules (funcionalidad básica)
include("Core/Types.jl")
include("Core/Evaluation.jl") 
include("Core/Display.jl")

# Analysis modules (análisis semántico)
include("Analysis/TruthTables.jl")
include("Analysis/Properties.jl")
include("Analysis/NormalForms.jl")

# Algorithm modules (algoritmos de decisión)
include("Algorithms/DPLL.jl")
include("Algorithms/Tableaux.jl")
include("Algorithms/Resolution.jl")

# ==================== IMPORTACIÓN DE SUBMÓDULOS ====================

using .Types
using .Evaluation
using .Display
using .TruthTables
using .Properties
using .NormalForms
using .DPLL_module
using .Tableaux
using .Resolution

# ==================== RE-EXPORTACIÓN PÚBLICA ====================

# Tipos fundamentales y constructores
export FormulaPL, Var_PL, Neg_PL, And_PL, Or_PL, Imp_PL, Iff_PL, Top_PL, Bottom_PL
export Valuation, Literal, Clause, Cube, TableauNode, ExtendedClause

# Constructores y utilidades básicas
export vars, ⊤, ⊥, ⋀, ⋁, @formula

# Operadores lógicos (ya exportados por tipos, pero explícito para claridad)
export &, |, !, >, ~

# Funciones de análisis básico
export vars_of, subformulas, evaluate, formation_tree

# Tablas de verdad y modelos
export truth_table, models, countermodels, print_table, all_valuations_for, valuation_from_binary

# Propiedades semánticas
export TAUT, SAT, UNSAT, LC_Def, LC_TAUT, LC_RA, EQUIV, EQUIV_models, simplify_constants

# Formas normales
export to_CNF, to_DNF, remove_imp, move_negation_in, dist_and_or, dist_or_and
export extract_clauses_from_CNF, extract_cubes_from_DNF, build_CNF_from_clauses, build_DNF_from_cubes
export formula_from_literal, complement, are_complementary, is_tautological, is_contradictory

# Algoritmo DPLL
export to_CF, clean_CF, apply_val, unit_clauses, pure_literals
export DPLL, DPLL_SAT, DPLL_solve, DPLL_LC

# Tableros semánticos
export TS, TS_SAT, TS_TAUT, TS_solve, print_TS
export has_contradiction, is_atomic, apply_α, apply_β, extract_literals
export DNF_from_TS, CNF_from_TS, plot_TS, save_TS_plot

# Resolución
export subsumes, remove_subsumed!, remove_tautologies!,
       simplify!, resolve, can_resolve, is_empty_clause,
       resolution_saturacion, compare_all_resolution_methods,
       resolution_regular, resolution_regular_auto,
       order_by_frequency, order_by_polarity_balance

export ResolutionStrategy, StrategyContext
export can_resolve_with_strategy

# Estrategias específicas de Resolución
export NoStrategy, PositiveStrategy, NegativeStrategy,
       LinearStrategy, UnitStrategy, InputStrategy

export resolution_with_strategy

export get_strategy_info, list_strategies, compare_strategies


# Funciones de conveniencia
export analyze, compare_algorithms, version

# ==================== FUNCIONES DE CONVENIENCIA ====================

"""
    analyze(f::FormulaPL; verbose::Bool = false)

Realiza un análisis completo de una fórmula usando los tres algoritmos 
principales.

# Análisis incluido:
1. Análisis sintáctico: variables, subfórmulas, árbol de formación, FNC/FND
2. Propiedades básicas (TAUT, SAT)
3. Tabla de verdad (si hay pocas variables), modelos y contramodelos
4. Verificación con DPLL
5. Verificación con Tableros Semánticos
6. Verificación con Resolución

# Argumentos
- `f`: Fórmula a analizar
- `verbose`: Mostrar detalles de cada algoritmo

# Ejemplos
```julia
formula = (p & q) | (!p & !q)
analyze(formula, verbose=true)
```
"""
function analyze(f::FormulaPL; verbose::Bool = false)
    println("="^60)
    println("ANÁLISIS COMPLETO DE FÓRMULA")
    println("="^60)
    println("Fórmula: $f")
    println()

    println("1. PROPIEDADES SINTÁCTICAS:\n")
    variables = vars_of(f)
    println("   $(length(vars_of(f))) Variables: ", join(variables, ", "))
    println()
    println("   Árbol de formación:")
    println("    ", formation_tree(f, "    ", true))
    sub = subformulas(f)
    println()
    println("   $(length(sub)) Subfórmulas: ")
    for s in sub
        println("      $s")
    end
    println()
    println("   FNC: ", to_CNF(f))
    println("   FND: ", to_DNF(f))
    println()


    # Análisis básico
    println("2. PROPIEDADES BÁSICAS:\n")
    sat = SAT(f)
    taut = TAUT(f)
    println("    Satisfactible: $(sat ? "✅ SÍ" : "❌ NO")")
    println("    Tautología:    $(taut ? "✅ SÍ" : "❌ NO")")
    
    if sat && !taut
        println("    Clasificación: CONTINGENTE")
    elseif !sat 
        println("    Clasificación: CONTRADICCIÓN") 
    elseif taut
        println("    Clasificación: TAUTOLOGÍA")
    end
    println()
    
    # Tabla de verdad (solo si hay pocas variables)
    if length(variables) <= 4
        println("3. TABLA DE VERDAD:\n")
        table = truth_table(f)
        print_table(table; tabs="    ")
        println()
    else
        println("3. TABLA DE VERDAD: Omitida (demasiadas variables: $(length(variables)))")
        println()
    end

    ms = models(f)
    cms = countermodels(f)
    println("   Modelos ($(length(ms))): ")
    for m in ms
        println("    $m")
    end
    println()
    println("   Contramodelos ($(length(cms))): ")
    for cm in cms
        println("    $cm")
    end
    println()

    println("4. APLICACIÓN DE ALGORITMOS:\n")
    # Verificación con DPLL
    dpll_result = DPLL(f, verbose=verbose)
    println("    Resultado DPLL: $(dpll_result[1] ? "SATISFACTIBLE" : "INSATISFACTIBLE")")
    
    # Verificación con Tableros Semánticos
    tableau, ms = TS(f)
    ts_result = !tableau.is_closed
    println("    Resultado TS: $(ts_result ? "SATISFACTIBLE" : "INSATISFACTIBLE")")
    if ts_result
        println("    Modelos encontrados:")
        for (i, m) in enumerate(ms)
            println("      Modelo $(i): $(⋀(m["literals"]))")
        end
    end
    
    # Verificación con Resolución
    cl = Set(to_CF(f))
    res_result = resolution_regular_auto(cl)
    println("    Resultado RES: $(res_result ? "SATISFACTIBLE" : "INSATISFACTIBLE")")
    println()
    
    println("="^60)
    return sat, taut
end

"""
    compare_algorithms(f::FormulaPL; iterations::Int = 1)

Compara el rendimiento de los tres algoritmos principales.

# Métricas comparadas:
- Tiempo de ejecución
- Uso de memoria (si está disponible)

# Argumentos
- `f`: Fórmula a analizar
- `iterations`: Número de repeticiones para el benchmark

# Utilidad
Permite evaluar qué algoritmo es más eficiente para diferentes tipos de fórmulas.
"""
function compare_algorithms(f::FormulaPL; iterations::Int = 1)
    println("="^60)
    println("COMPARACIÓN DE ALGORITMOS")
    println("="^60)
    println("Fórmula: $f")
    println("Iteraciones: $iterations")
    println()
    
    # Benchmark DPLL
    print("Ejecutando DPLL... ")
    dpll_time = @elapsed begin
        dpll_result = nothing
        for _ in 1:iterations
            dpll_result = DPLL(f, verbose=false)
        end
    end
    dpll_time /= iterations
    println("✓")
    
    # Benchmark Tableros Semánticos
    print("Ejecutando Tableros Semánticos... ")
    ts_time = @elapsed begin
        ts_result = nothing
        for _ in 1:iterations
            ts_result, ms = TS_SAT(f)
        end
    end
    ts_time /= iterations
    println("✓")
    
    # Benchmark Resolución
    print("Ejecutando Resolución... ")
    res_time = @elapsed begin
        res_result = nothing
        cl = Set(to_CF(f))
        for _ in 1:iterations
            res_result = resolution_saturacion(cl, verbose=false)
        end
    end
    res_time /= iterations
    println("✓")
    
    # Mostrar resultados
    println("\nRESULTADOS:")
    println("Algorithm               Tiempo (s)    Resultado")
    println("-" ^ 50)
    println("DPLL                      $(lpad(string(round(dpll_time, digits=6)), 10))    $(dpll_result[1] ? "SAT" : "UNSAT")")
    println("Tableros Semánticos       $(lpad(string(round(ts_time, digits=6)), 10))    $(ts_result ? "SAT" : "UNSAT")")
    println("Resolución                $(lpad(string(round(res_time, digits=6)), 10))    $(res_result ? "SAT" : "UNSAT")")
    
    # Identificar el más rápido
    times = [("DPLL", dpll_time), ("Tableros", ts_time), ("Resolución", res_time)]
    fastest = times[argmin([x[2] for x in times])]
    println("\n🏆 Algoritmo más rápido: $(fastest[1]) ($(round(fastest[2], digits=6))s)")
    
    println("="^60)
    return (dpll_result, dpll_time), (ts_result, ts_time), (res_result, res_time)
end

"""
    verify_logical_consequence(premises::Vector{FormulaPL}, conclusion::FormulaPL; verbose::Bool = false)

Verifica consecuencia lógica usando los tres métodos principales.

# Métodos utilizados:
1. Definición semántica (modelos)
2. DPLL (reducción al absurdo)
3. Resolución (insatisfactibilidad)

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
premises = [p > q, q > r]
conclusion = p > r
verify_logical_consequence(premises, conclusion, verbose=true)
```
"""
function verify_logical_consequence(premises::Vector{FormulaPL}, conclusion::FormulaPL; verbose::Bool = false)
    println("="^60)
    println("VERIFICACIÓN DE CONSECUENCIA LÓGICA")
    println("="^60)
    println("Premisas:")
    for (i, p) in enumerate(premises)
        println("  P$i: $p")
    end
    println("Conclusión: $conclusion")
    println()
    
    # Método 1: Definición semántica
    println("1. MÉTODO: Definición semántica (modelos)")
    result1 = LC_Def(premises, conclusion)
    println("   Resultado: $(result1 ? "✅ ES consecuencia" : "❌ NO ES consecuencia")")
    println()
    
    # Método 2: DPLL
    println("2. MÉTODO: DPLL (reducción al absurdo)")
    result2 = DPLL_LC(premises, conclusion, verbose=verbose)
    println("   Resultado: $(result2 ? "✅ ES consecuencia" : "❌ NO ES consecuencia")")
    println()
    
    # Método 3: Resolución
    println("3. MÉTODO: Resolución (insatisfactibilidad)")
    result3 = RES_LC(premises, conclusion, verbose=verbose)
    println("   Resultado: $(result3 ? "✅ ES consecuencia" : "❌ NO ES consecuencia")")
    println()
    
    # Verificar consistencia
    if result1 == result2 == result3
        println("✅ CONSISTENCIA: Todos los métodos concuerdan")
        println("CONCLUSIÓN FINAL: $(result1 ? "ES" : "NO ES") consecuencia lógica")
    else
        println("❌ INCONSISTENCIA: Los métodos difieren")
        println("   Definición: $result1")
        println("   DPLL: $result2")
        println("   Resolución: $result3")
    end
    
    println("="^60)
    return result1, result2, result3
end

# ==================== INFORMACIÓN DEL MÓDULO ====================

"""
    version()

Muestra información sobre la versión y estructura del módulo.
"""
function version()
    println("PropositionalLogic.jl v1.2")
    println("Módulo de Lógica Proposicional")
    println("Autor: Fernando Sancho Caparrini")
    println("Fecha: 20-10-2025")
    println("Universidad de Sevilla")
    println()
    println("Submódulos incluidos:")
    println("  Core: Types, Evaluation, Display")
    println("  Analysis: TruthTables, Properties, NormalForms")
    println("  Algorithms: DPLL, Tableaux, Resolution")
    println()
    # println("Uso: help(PropositionalLogic) para documentación completa")
end

# Mostrar información al cargar el módulo
function __init__()
    println("PropositionalLogic.jl cargado exitosamente")
    println("Usar version() para información del módulo")
    println("Usar analyze(f) para análisis completo")
end

end # module PropositionalLogic
