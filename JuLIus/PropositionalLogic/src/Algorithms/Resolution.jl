"""
# Algorithms.Resolution - Algoritmo de Resolución

Este submódulo implementa el algoritmo de resolución para la verificación
de satisfactibilidad de fórmulas en forma clausal (CF).

## Descripción del algoritmo:
La resolución es un método refutacional que busca derivar la cláusula vacía
(contradicción) a partir de un conjunto de cláusulas.

## Principio de resolución:
Dadas dos cláusulas que contienen literales complementarios, se puede
inferir una nueva cláusula (resolvente) que combina el resto de literales.

## Regla de resolución:
- C₁ ∨ p, C₂ ∨ ¬p ⊢ C₁ ∨ C₂
- Si C₁ = ∅ y C₂ = ∅, entonces la resolvente es ☐ (cláusula vacía)

## Aplicaciones:
- Verificación de satisfactibilidad (SAT)
- Verificación de consecuencia lógica
- Demostración automática de teoremas
- Fundamento de la programación lógica

## Ventajas:
- Completo y correcto
- Mecanizable
- Base teórica sólida

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module Resolution

using ..Types
using ..Evaluation
using ..NormalForms
using ..DPLL_module
import Base: show

export subsumes, remove_subsumed!, remove_tautologies!,
       simplify!, resolve, can_resolve, is_empty_clause,
       resolution_saturacion, compare_all_resolution_methods,
       resolution_regular, resolution_regular_auto,
       order_by_frequency, order_by_polarity_balance
# Sistema de estrategias
export ResolutionStrategy, StrategyContext
export can_resolve_with_strategy

# Estrategias específicas
export NoStrategy, PositiveStrategy, NegativeStrategy, 
       LinearStrategy, UnitStrategy, InputStrategy

# Resolución con estrategias
export resolution_with_strategy

# Utilidades de estrategias
export get_strategy_info, list_strategies, compare_strategies


"""
    subsumes(c1::Clause, c2::Clause)

Verifica si c1 subsume a c2.
c1 subsume a c2 si todos los literales de c1 están en c2.

# Interpretación Lógica
Si c1 ⊆ c2, entonces c2 es más débil (menos informativa) que c1.
Podemos eliminar c2 porque c1 ya implica c2.

# Ejemplo
{P} subsume {P, Q} → podemos eliminar {P, Q}
{P, Q} no subsume {P, R}
"""
function subsumes(c1::Clause, c2::Clause)
    # c1 subsume c2 si c1 ⊆ c2
    return issubset(c1.literals, c2.literals)
end

"""
    remove_subsumed!(clauses::Set{Clause})

Elimina todas las cláusulas subsumidas del conjunto.
Modifica el conjunto in-place.

# Retorna
Número de cláusulas eliminadas
"""
function remove_subsumed!(clauses::Set{Clause})
    to_remove = Set{Clause}()
    clauses_vec = collect(clauses)
    
    for i in 1:length(clauses_vec)
        if clauses_vec[i] ∈ to_remove
            continue
        end
        
        for j in 1:length(clauses_vec)
            if i == j || clauses_vec[j] ∈ to_remove
                continue
            end
            
            # Si clauses_vec[i] subsume clauses_vec[j], eliminar j
            if subsumes(clauses_vec[i], clauses_vec[j])
                push!(to_remove, clauses_vec[j])
            end
        end
    end
    
    # Eliminar cláusulas subsumidas
    setdiff!(clauses, to_remove)
    
    return length(to_remove)
end

"""
    remove_tautologies!(clauses::Set{Clause})

Elimina todas las tautologías del conjunto.
Modifica el conjunto in-place.

# Retorna
Número de tautologías eliminadas
"""
function remove_tautologies!(clauses::Set{Clause})
    to_remove = Set{Clause}()
    
    for clause in clauses
        if is_tautological(clause)
            push!(to_remove, clause)
        end
    end
    
    setdiff!(clauses, to_remove)
    
    return length(to_remove)
end

"""
    simplify!(clauses::Set{Clause})

Simplifica un conjunto de cláusulas eliminando tautologías y cláusulas subsumidas.
Modifica el conjunto in-place.

# Retorna
Tupla (num_tautologies, num_subsumed) con el número de cláusulas eliminadas
"""
function simplify!(clauses::Set{Clause})
    num_taut = remove_tautologies!(clauses)
    num_subs = remove_subsumed!(clauses)
    return (num_taut, num_subs)
end

"""
    resolve(c1::Clause, c2::Clause, var::Var_PL)

Aplica la regla de resolución entre dos cláusulas sobre una variable.

# Argumentos
- `c1::Clause`: Primera cláusula (contiene var positivo)
- `c2::Clause`: Segunda cláusula (contiene var negativo)
- `var::Var_PL`: Variable sobre la cual resolver

# Retorna
- `Clause`: Resolvente (unión de literales sin los complementarios)
- `nothing`: Si no se puede resolver (var no aparece complementaria)

# Ejemplo
Si c1 = {P, Q} y c2 = {¬P, R}, resolver sobre P da {Q, R}
"""
function resolve(c1::Clause, c2::Clause, var::Var_PL)
    # Buscar literales complementarios
    lit_pos = Literal(var, true)
    lit_neg = Literal(var, false)
    
    has_pos_in_c1 = lit_pos ∈ c1.literals
    has_neg_in_c1 = lit_neg ∈ c1.literals
    has_pos_in_c2 = lit_pos ∈ c2.literals
    has_neg_in_c2 = lit_neg ∈ c2.literals
    
    # Verificar que la variable aparece complementaria entre c1 y c2
    can_resolve = (has_pos_in_c1 && has_neg_in_c2) || 
                  (has_neg_in_c1 && has_pos_in_c2)
    
    if !can_resolve
        return nothing
    end
    
    # Crear resolvente: unión sin los literales complementarios
    new_literals = Set{Literal}()
    
    for lit in c1.literals
        if lit.variable != var
            push!(new_literals, lit)
        end
    end
    
    for lit in c2.literals
        if lit.variable != var
            push!(new_literals, lit)
        end
    end
    
    return Clause(new_literals)
end

"""
    can_resolve(c1::Clause, c2::Clause)

Verifica si dos cláusulas pueden resolverse.

# Retorna
- `Vector{Var_PL}`: Variables sobre las cuales se puede resolver
"""
function can_resolve(c1::Clause, c2::Clause)
    resolvable_vars = Var_PL[]
    
    # Extraer variables de ambas cláusulas
    vars_c1 = Set(lit.variable for lit in c1.literals)
    vars_c2 = Set(lit.variable for lit in c2.literals)
    
    # Buscar variables que aparecen complementarias
    for var in intersect(vars_c1, vars_c2)
        lit_pos = Literal(var, true)
        lit_neg = Literal(var, false)
        
        has_pos_c1 = lit_pos ∈ c1.literals
        has_neg_c1 = lit_neg ∈ c1.literals
        has_pos_c2 = lit_pos ∈ c2.literals
        has_neg_c2 = lit_neg ∈ c2.literals
        
        # Variable aparece complementaria entre c1 y c2
        if (has_pos_c1 && has_neg_c2) || (has_neg_c1 && has_pos_c2)
            push!(resolvable_vars, var)
        end
    end
    
    return resolvable_vars
end



"""
    is_empty_clause(c::Clause)

Verifica si una cláusula es la cláusula vacía (contradicción).
"""
is_empty_clause(c::Clause) = isempty(c.literals)


"""
    resolution_saturacion(clauses::Set{Clause}; verbose=false)

Aplica el algoritmo de resolución por saturación para determinar 
si un conjunto de cláusulas es insatisfacible.

# Algoritmo
1. S = conjunto inicial de cláusulas
2. Repetir:
   - Seleccionar dos cláusulas que puedan resolverse
   - Generar resolvente
   - Si resolvente es ☐, retornar INSATISFACIBLE
   - Si resolvente es nuevo, agregarlo a S
3. Si no se pueden generar más resolventes, retornar SATISFACIBLE

Versión optimizada del algoritmo de resolución con:
- Eliminación de tautologías
- Eliminación de cláusulas subsumidas
- Simplificación incremental

# Argumentos
- `clauses::Set{Clause}`: Conjunto inicial de cláusulas
- `verbose::Bool`: Si true, muestra información de progreso

# Retorna
- `false`: Si el conjunto es insatisfacible (se deriva ☐)
- `true`: Si el conjunto es satisfacible (saturación sin ☐)

"""
function resolution_saturacion(clauses::Set{Clause}; verbose=false)
    # Simplificación inicial
    S = copy(clauses)
    simplify!(S)
    
    if verbose
        println("Conjunto inicial (simplificado): $(length(S)) cláusulas")
        println("Cláusulas iniciales:")
         for clause in S
               println("  ", clause)
         end
    end
    
    new_clauses = copy(S)
    iteration = 0
    
    while !isempty(new_clauses)
        iteration += 1
        current = pop!(new_clauses)
        
        if verbose && iteration % 100 == 0
            println("Iteración $iteration: $(length(S)) cláusulas, $(length(new_clauses)) nuevas")
        end
        
        for clause in S
            if clause === current
                continue
            end
            
            # Intentar resolver sobre todas las variables posibles
            resolvable_vars = can_resolve(current, clause)
            
            for var in resolvable_vars
                resolvente = resolve(current, clause, var)
                
                if resolvente === nothing
                    continue
                end
                
                # Si encontramos la cláusula vacía: INSATISFACIBLE
                if is_empty_clause(resolvente)
                    if verbose
                        println("☐ Cláusula vacía encontrada en iteración $iteration")
                        println("     ☐ = Res( $current , $clause , $var )")
                    end
                    return false
                end
                
                # Ignorar tautologías
                if is_tautological(resolvente)
                    continue
                end
                
                # Verificar si el resolvente subsume alguna cláusula existente
                # o si es subsumido por alguna cláusula existente
                is_subsumed = false
                subsumes_others = Set{Clause}()
                
                for existing in S
                    if subsumes(existing, resolvente)
                        # El resolvente es subsumido, no agregarlo
                        is_subsumed = true
                        break
                    elseif subsumes(resolvente, existing)
                        # El resolvente subsume una cláusula existente
                        push!(subsumes_others, existing)
                    end
                end
                
                if is_subsumed
                    continue
                end
                
                # Agregar el resolvente solo si es nuevo
                if resolvente ∉ S
                  if verbose
                        println("Nueva resolvente: $resolvente = Res( $current , $clause , $var )")
                    end
                  push!(S, resolvente)
                  push!(new_clauses, resolvente)
                    
                  # Eliminar cláusulas subsumidas por el nuevo resolvente
                  if !isempty(subsumes_others)
                     setdiff!(S, subsumes_others)
                     setdiff!(new_clauses, subsumes_others)
                  end
                end
            end
        end
        
        # Simplificación periódica (cada N iteraciones)
        if iteration % 1 == 0
            old_size = length(S)
            simplify!(S)
            if verbose && length(S) < old_size
                println("  Simplificación: $(old_size) → $(length(S)) cláusulas")
            end
        end
    end
    
    if verbose
        println("Saturación alcanzada en $iteration iteraciones con $(length(S)) cláusulas")
        for clause in S
            println("  ", clause)
        end
    end
    
    # Saturación alcanzada sin derivar ☐: SATISFACIBLE
    return true
end

"""
    resolution_regular(clauses::Set{Clause}, var_order::Vector{Var_PL}; verbose=false)

Algoritmo de resolución ordenada.

# Algoritmo
1. Se fija un orden total sobre las variables: v₁ < v₂ < ... < vₙ
2. Para cada variable vᵢ en orden:
   - Resolver todas las cláusulas que contienen vᵢ (positivo o negativo)
   - Eliminar todas las cláusulas que contienen vᵢ
   - Añadir los resolventes (que no contienen vᵢ)
3. Si se obtiene la cláusula vacía: INSATISFACIBLE
4. Si se eliminan todas las cláusulas: SATISFACIBLE

# Argumentos
- `clauses::Set{Clause}`: Conjunto inicial de cláusulas
- `var_order::Vector{Var_PL}`: Orden de las variables para resolución
- `verbose::Bool`: Mostrar información de progreso

# Retorna
- `true`: Si el conjunto es insatisfacible (se deriva ☐)
- `false`: Si el conjunto es satisfacible (conjunto vacío)
"""
function resolution_regular(clauses::Set{Clause}, var_order::Vector{Var_PL}; verbose=false)
    S = copy(clauses)
    
    # Simplificación inicial
    simplify!(S)
    
    if verbose
        println("=== RESOLUCIÓN REGULAR ===")
        println("Orden de variables: ", join(var_order, " < "))
        println("Conjunto inicial: $(length(S)) cláusulas\n")
    end
    
    # Procesar cada variable en orden
    for (idx, var) in enumerate(var_order)
        if verbose
            println("--- Variable $idx/$(length(var_order)): $var ---")
            println("Cláusulas antes: $(length(S))")
            println("     { ", join(S, " , "), " }")
        end
        
        # Separar cláusulas que contienen var (positivo o negativo)
        clauses_with_var = Set{Clause}()
        clauses_without_var = Set{Clause}()
        
        for clause in S
            contains_var = any(lit.variable == var for lit in clause.literals)
            if contains_var
                push!(clauses_with_var, clause)
            else
                push!(clauses_without_var, clause)
            end
        end
        
        if verbose
            println("  Cláusulas sin $var:  { ", join(clauses_without_var, " , "), " }")
            println("  Cláusulas con $var:")
        end
        
        # Si no hay cláusulas con esta variable, continuar
        if isempty(clauses_with_var)
            if verbose
                println("  (variable no aparece, continuar)\n")
            end
            continue
        end
        
        # Separar cláusulas con literal positivo y negativo
        clauses_pos = Set{Clause}()
        clauses_neg = Set{Clause}()
        
        for clause in clauses_with_var
            has_pos = Literal(var, true) ∈ clause.literals
            has_neg = Literal(var, false) ∈ clause.literals
            
            if has_pos
                push!(clauses_pos, clause)
            end
            if has_neg
                push!(clauses_neg, clause)
            end
        end
        
        if verbose
            println("      Positivas ($var):   { ", join(clauses_pos, " , "), " }")
            println("      Negativas (¬$var):   { ", join(clauses_neg, " , "), " }")
        end
        
        # Generar todos los resolventes entre cláusulas positivas y negativas
        resolvents = Set{Clause}()
        
        for c_pos in clauses_pos
            for c_neg in clauses_neg
                resolvent = resolve(c_pos, c_neg, var)
                
                if resolvent !== nothing
                    # Si obtenemos la cláusula vacía: INSATISFACIBLE
                    if is_empty_clause(resolvent)
                        if verbose
                            println("  ☐ Cláusula vacía obtenida!")
                            println("    Resolviendo: $c_pos y $c_neg")
                            println("\n=== RESULTADO: INSATISFACIBLE ===")
                        end
                        return false
                    end
                    
                    # Ignorar tautologías
                    if !is_tautological(resolvent)
                        push!(resolvents, resolvent)
                    end
                end
            end
        end
        
        if verbose
            println("  Resolventes generadas con $var:   { ", join(resolvents, " , "), " }")
        end
        
        # Actualizar S: eliminar cláusulas con var, añadir resolventes
        S = union(clauses_without_var, resolvents)
        
        # Simplificar (eliminar tautologías y subsunciones)
        old_size = length(S)
        simplify!(S)
        
        if verbose
            if length(S) < old_size
                println("  Simplificación: $old_size → $(length(S))")
            end
            println("Cláusulas después: $(length(S))\n")
        end
        
        # Si no quedan cláusulas: SATISFACIBLE
        if isempty(S)
            if verbose
                println("=== RESULTADO: SATISFACIBLE (conjunto vacío) ===")
            end
            return true
        end
    end
    
    return true
end

"""
    extract_variables(clauses::Set{Clause})

Extrae todas las variables que aparecen en un conjunto de cláusulas.

# Retorna
Vector de variables en orden arbitrario
"""
function extract_variables(clauses::Set{Clause})
    vars = Set{Var_PL}()
    for clause in clauses
        for lit in clause.literals
            push!(vars, lit.variable)
        end
    end
    return collect(vars)
end

"""
    resolution_regular_auto(clauses::Set{Clause}; 
                           var_order::Union{Vector{Var_PL}, Nothing}=nothing,
                           verbose=false)

Resolución ordenada con orden automático de variables si no se proporciona.

# Argumentos
- `clauses::Set{Clause}`: Conjunto de cláusulas
- `var_order::Union{Vector{Var_PL}, Nothing}`: Orden de variables (si es nothing, se genera automáticamente)
- `verbose::Bool`: Mostrar información

# Estrategias de ordenación automática
Si no se proporciona orden, se puede usar:
1. Orden alfabético/lexicográfico
2. Orden por frecuencia (más frecuente primero)
3. Orden aleatorio

# Retorna
- `true`: INSATISFACIBLE
- `false`: SATISFACIBLE
"""
function resolution_regular_auto(clauses::Set{Clause}; 
                                var_order::Union{Vector{Var_PL}, Nothing}=nothing,
                                verbose=false)
    # Si no se proporciona orden, extraer y ordenar alfabéticamente
    if var_order === nothing
        vars = extract_variables(clauses)
        var_order = sort(collect(vars))
    end
    
    return resolution_regular(clauses, var_order, verbose=verbose)
end


"""
    order_by_frequency(clauses::Set{Clause})

Ordena variables por frecuencia de aparición (más frecuente primero).
"""
function order_by_frequency(clauses::Set{Clause})
    freq = Dict{Var_PL, Int}()
    
    for clause in clauses
        for lit in clause.literals
            freq[lit.variable] = get(freq, lit.variable, 0) + 1
        end
    end
    
    # Ordenar por frecuencia descendente
    sorted_vars = sort(collect(keys(freq)), by=v -> -freq[v])
    return sorted_vars
end

"""
    order_by_polarity_balance(clauses::Set{Clause})

Ordena variables por balance de polaridad.
Variables con más balance (similar número de apariciones positivas y negativas)
aparecen primero.
"""
function order_by_polarity_balance(clauses::Set{Clause})
    pos_count = Dict{Var_PL, Int}()
    neg_count = Dict{Var_PL, Int}()
    
    for clause in clauses
        for lit in clause.literals
            if lit.positive
                pos_count[lit.variable] = get(pos_count, lit.variable, 0) + 1
            else
                neg_count[lit.variable] = get(neg_count, lit.variable, 0) + 1
            end
        end
    end
    
    vars = union(keys(pos_count), keys(neg_count))
    
    # Calcular balance (menor diferencia = más balanceado)
    balance_score = Dict{Var_PL, Float64}()
    for var in vars
        pos = get(pos_count, var, 0)
        neg = get(neg_count, var, 0)
        total = pos + neg
        # Balance: 0.0 = perfectamente balanceado, 1.0 = completamente desbalanceado
        balance_score[var] = abs(pos - neg) / total
    end
    
    # Ordenar por balance ascendente (más balanceado primero)
    sorted_vars = sort(collect(vars), by=v -> balance_score[v])
    return sorted_vars
end


"""
    compare_all_resolution_methods(clauses::Set{Clause}; verbose=false)

Compara todos los métodos de resolución implementados.
"""
function compare_all_resolution_methods(clauses::Set{Clause}; verbose=false)
    println("\n" * "="^70)
    println("COMPARACIÓN: Métodos de Resolución")
    println("="^70)
    
    results = Dict{String, Any}()
    # 1. Resolución saturación
    println("\n[1] RESOLUCIÓN SATURACIÓN")
    println("-"^70)
    test_set = copy(clauses)
    time_std = @elapsed result_std = resolution_saturacion(test_set, verbose=verbose)
    results["Saturación"] = (result_std, time_std)

    # 2. Resolución regular (orden alfabético)
    println("\n[2] RESOLUCIÓN REGULAR (orden alfabético)")
    println("-"^70)
    test_set = copy(clauses)
    var_order_alpha = sort(collect(extract_variables(clauses)))
    time_ord_alpha = @elapsed result_ord_alpha = resolution_regular(test_set, var_order_alpha, verbose=verbose)
    results["Regular (alfabético)"] = (result_ord_alpha, time_ord_alpha)

    # 3. Resolución regular (por frecuencia)
    println("\n[3] RESOLUCIÓN REGULAR (por frecuencia)")
    println("-"^70)
    test_set = copy(clauses)
    var_order_freq = order_by_frequency(clauses)
    time_ord_freq = @elapsed result_ord_freq = resolution_regular(test_set, var_order_freq, verbose=verbose)
    results["Regular (frecuencia)"] = (result_ord_freq, time_ord_freq)

    # 4. Resolución regular (por balance de polaridad)
    println("\n[4] RESOLUCIÓN REGULAR (por balance)")
    println("-"^70)
    test_set = copy(clauses)
    var_order_bal = order_by_polarity_balance(clauses)
    time_ord_bal = @elapsed result_ord_bal = resolution_regular(test_set, var_order_bal, verbose=verbose)
    results["Regular (balance)"] = (result_ord_bal, time_ord_bal)
    
    # Resumen
    println("\n" * "="^70)
    println("RESUMEN")
    println("="^70)
    println(rpad("Método", 30), rpad("Resultado", 20), "Tiempo (ms)")
    println("-"^70)
    
    for (method, (result, time)) in results
        result_str = result ? "INSATISFACIBLE" : "SATISFACIBLE"
        println(rpad(method, 30), rpad(result_str, 20), round(time * 1000, digits=2))
    end
    
    println("="^70)
end

# ============================================================================
# RESOLUCIÓN CON ESTRATEGIAS
# ============================================================================

"""
    ResolutionStrategy

Tipo abstracto para definir estrategias de resolución.
Cada estrategia determina qué pares de cláusulas pueden resolverse.
"""
abstract type ResolutionStrategy end

"""
    can_resolve_with_strategy(strategy::ResolutionStrategy, c1::Clause, c2::Clause, context)

Verifica si dos cláusulas pueden resolverse bajo una estrategia específica.

# Argumentos
- `strategy::ResolutionStrategy`: La estrategia a aplicar
- `c1::Clause`: Primera cláusula
- `c2::Clause`: Segunda cláusula
- `context`: Contexto adicional (información sobre cláusulas originales, última resolvente, etc.)

# Retorna
- `Bool`: true si las cláusulas pueden resolverse bajo la estrategia
"""
function can_resolve_with_strategy end

"""
    StrategyContext

Contexto para mantener información necesaria para las estrategias.

# Campos
- `original_clauses::Set{Clause}`: Conjunto original de cláusulas (para estrategia por entradas)
- `last_resolvent::Union{Clause, Nothing}`: Última resolvente generada (para estrategia lineal)
- `all_generated::Set{Clause}`: Todas las cláusulas generadas hasta ahora
"""
mutable struct StrategyContext
    original_clauses::Set{Clause}
    last_resolvent::Union{Clause, Nothing}
    all_generated::Set{Clause}
end

StrategyContext(original::Set{Clause}) = StrategyContext(original, nothing, copy(original))

# ============================================================================
# ESTRATEGIAS ESPECÍFICAS
# ============================================================================

"""
    NoStrategy <: ResolutionStrategy

Sin restricciones: cualquier par de cláusulas puede resolverse.
Equivale a resolución estándar.
"""
struct NoStrategy <: ResolutionStrategy end

function can_resolve_with_strategy(::NoStrategy, c1::Clause, c2::Clause, context::StrategyContext)
    return true
end

"""
    PositiveStrategy <: ResolutionStrategy

Estrategia positiva: al menos una de las dos cláusulas debe tener todos sus literales positivos.
"""
struct PositiveStrategy <: ResolutionStrategy end

"""
    is_positive_clause(c::Clause)

Verifica si una cláusula tiene todos sus literales positivos.
"""
function is_positive_clause(c::Clause)
    return all(lit.positive for lit in c.literals)
end

function can_resolve_with_strategy(::PositiveStrategy, c1::Clause, c2::Clause, context::StrategyContext)
    return is_positive_clause(c1) || is_positive_clause(c2)
end

"""
    NegativeStrategy <: ResolutionStrategy

Estrategia negativa: al menos una de las dos cláusulas debe tener todos sus literales negativos.
"""
struct NegativeStrategy <: ResolutionStrategy end

"""
    is_negative_clause(c::Clause)

Verifica si una cláusula tiene todos sus literales negativos.
"""
function is_negative_clause(c::Clause)
    return all(!lit.positive for lit in c.literals)
end

function can_resolve_with_strategy(::NegativeStrategy, c1::Clause, c2::Clause, context::StrategyContext)
    return is_negative_clause(c1) || is_negative_clause(c2)
end

"""
    LinearStrategy <: ResolutionStrategy

Estrategia lineal: al menos una de las dos cláusulas debe ser la última resolvente generada.
En la primera iteración (cuando no hay resolvente previa), puede resolver cualquier par.
"""
struct LinearStrategy <: ResolutionStrategy end

function can_resolve_with_strategy(::LinearStrategy, c1::Clause, c2::Clause, context::StrategyContext)
    # Si no hay resolvente previa (inicio), permitir cualquier resolución
    if context.last_resolvent === nothing
        return true
    end
    
    # Al menos una debe ser la última resolvente
    return c1 == context.last_resolvent || c2 == context.last_resolvent
end

"""
    UnitStrategy <: ResolutionStrategy

Estrategia unitaria: al menos una de las dos cláusulas debe ser unitaria (un solo literal).
"""
struct UnitStrategy <: ResolutionStrategy end

"""
    is_unit_clause(c::Clause)

Verifica si una cláusula es unitaria (tiene un solo literal).
"""
function is_unit_clause(c::Clause)
    return length(c.literals) == 1
end

function can_resolve_with_strategy(::UnitStrategy, c1::Clause, c2::Clause, context::StrategyContext)
    return is_unit_clause(c1) || is_unit_clause(c2)
end

"""
    InputStrategy <: ResolutionStrategy

Estrategia por entradas: al menos una de las dos cláusulas debe ser del conjunto original.
"""
struct InputStrategy <: ResolutionStrategy end

function can_resolve_with_strategy(::InputStrategy, c1::Clause, c2::Clause, context::StrategyContext)
    return c1 ∈ context.original_clauses || c2 ∈ context.original_clauses
end

# ============================================================================
# ALGORITMO DE RESOLUCIÓN CON ESTRATEGIAS
# ============================================================================

"""
    resolution_with_strategy(clauses::Set{Clause}, strategy::ResolutionStrategy; verbose=false)

Algoritmo de resolución aplicando una estrategia específica.

# Argumentos
- `clauses::Set{Clause}`: Conjunto inicial de cláusulas
- `strategy::ResolutionStrategy`: Estrategia de resolución a aplicar
- `verbose::Bool`: Mostrar información de progreso

# Retorna
- `true`: Si el conjunto es insatisfacible (se deriva ☐)
- `false`: Si el conjunto es satisfacible (saturación sin ☐)
"""
function resolution_with_strategy(clauses::Set{Clause}, strategy::ResolutionStrategy; verbose=false)
    S = copy(clauses)
    
    # Simplificación inicial
    simplify!(S)
    
    # Crear contexto para la estrategia
    context = StrategyContext(copy(S))
    
    if verbose
        strategy_name = typeof(strategy)
        println("=== RESOLUCIÓN CON ESTRATEGIA: $strategy_name ===")
        println("Conjunto inicial (simplificado): $(length(S)) cláusulas")
        println("     { ", join(S, " , "), " }\n")

    end
    
    new_clauses = copy(S)
    iteration = 0
    resolutions_attempted = 0
    resolutions_blocked = 0
    
    while !isempty(new_clauses)
        iteration += 1
        current = pop!(new_clauses)
        
        if verbose && iteration % 100 == 0
            println("Iteración $iteration: $(length(S)) cláusulas, $(length(new_clauses)) nuevas")
            println("  Resoluciones bloqueadas por estrategia: $resolutions_blocked")
        end
        
        for clause in S
            if clause === current
                continue
            end
            
            # Verificar si el par puede resolverse bajo la estrategia
            if !can_resolve_with_strategy(strategy, current, clause, context)
                resolutions_attempted += 1
                resolutions_blocked += 1
                continue
            end
            
            # Intentar resolver sobre todas las variables posibles
            resolvable_vars = can_resolve(current, clause)
            
            for var in resolvable_vars
                resolutions_attempted += 1
                resolvente = resolve(current, clause, var)
                
                if resolvente === nothing
                    continue
                end
                
                # Si encontramos la cláusula vacía: INSATISFACIBLE
                if is_empty_clause(resolvente)
                    if verbose
                        println("☐ Cláusula vacía encontrada en iteración $iteration")
                        println("   ☐ = Re( $current , $clause , $var )")
                        println("  Resoluciones intentadas: $resolutions_attempted")
                        println("  Bloqueadas por estrategia: $resolutions_blocked")
                    end
                    return true
                end
                
                # Ignorar tautologías
                if is_tautological(resolvente)
                    continue
                end
                
                # Verificar subsunción
                is_subsumed = false
                subsumes_others = Set{Clause}()
                
                for existing in S
                    if subsumes(existing, resolvente)
                        is_subsumed = true
                        break
                    elseif subsumes(resolvente, existing)
                        push!(subsumes_others, existing)
                    end
                end
                
                if is_subsumed
                    continue
                end
                
                # Agregar el resolvente solo si es nuevo
                if resolvente ∉ S
                    if verbose
                        println("Nueva resolvente: $resolvente = Res( $current , $clause , $var )")
                    end
                    push!(S, resolvente)
                    push!(new_clauses, resolvente)
                    push!(context.all_generated, resolvente)
                    
                    # Actualizar última resolvente para estrategia lineal
                    context.last_resolvent = resolvente
                    
                    # Eliminar cláusulas subsumidas
                    if !isempty(subsumes_others)
                        setdiff!(S, subsumes_others)
                        setdiff!(new_clauses, subsumes_others)
                    end
                end
            end
        end
        
        # Simplificación periódica
        if iteration % 50 == 0
            old_size = length(S)
            simplify!(S)
            if verbose && length(S) < old_size
                println("  Simplificación: $old_size → $(length(S))")
            end
        end
    end
    
    if verbose
        println("Saturación alcanzada en $iteration iteraciones con $(length(S)) cláusulas")
        println("Resoluciones totales intentadas: $resolutions_attempted")
        println("Bloqueadas por estrategia: $resolutions_blocked")
        rate = resolutions_blocked / max(resolutions_attempted, 1) * 100
        println("Tasa de bloqueo: $(round(rate, digits=2))%")
    end
    
    return false
end



# ============================================================================
# COMPARACIÓN DE ESTRATEGIAS
# ============================================================================

"""
    compare_strategies(clauses::Set{Clause}; verbose=false)

Compara todas las estrategias de resolución implementadas.
"""
function compare_strategies(clauses::Set{Clause}; verbose=false)
    println("\n" * "="^80)
    println("COMPARACIÓN DE ESTRATEGIAS DE RESOLUCIÓN")
    println("="^80)
    
    strategies = [
        ("Sin estrategia", NoStrategy(), true),
        ("Positiva", PositiveStrategy(), true),
        ("Negativa", NegativeStrategy(), true),
        ("Lineal", LinearStrategy(), true),
        ("Unitaria", UnitStrategy(), false),
        ("Por entradas", InputStrategy(), false)
    ]
    
    results = Dict{String, Tuple{Bool, Float64, Bool}}()
    
    for (name, strategy, complete) in strategies
        println("\n[$name]")
        println("-"^80)
        test_set = copy(clauses)
        time_taken = @elapsed result = resolution_with_strategy(test_set, strategy, verbose=verbose)
        results[name] = (result, time_taken, complete)
    end
    
    # Resumen
    println("\n" * "="^80)
    println("RESUMEN COMPARATIVO")
    println("="^80)
    println(rpad("Estrategia", 25), rpad("Resultado", 20), rpad("Tiempo (ms)", 15), "Completa")
    println("-"^80)
    
    for (name, (result, time, complete)) in results
        result_str = result ? "INSATISFACIBLE" : "SATISFACIBLE"
        time_str = string(round(time * 1000, digits=2))
        # Una estrategia es completa si encuentra INSATISFACIBLE cuando debe
        complete_str = complete ? "✓" : "✗"
        println(rpad(name, 25), rpad(result_str, 20), rpad(time_str, 15), complete_str)
    end
    
    println("\n" * "="^80)
    println("NOTAS:")
    println("• Estrategias marcadas con ✓ son completas (mismo resultado que sin estrategia)")
    println("• Estrategias marcadas con ✗ pueden no ser refutacionalmente completas (mirar cláusuas de Horn)")
    println("• Todas las estrategias son correctas (si encuentran ☐, es INSATISFACIBLE)")
    println("="^80)
end

"""
    get_strategy_info(strategy::ResolutionStrategy)

Retorna información descriptiva sobre una estrategia.
"""
function get_strategy_info(strategy::ResolutionStrategy)
    info = Dict(
        NoStrategy => "Sin restricciones: cualquier par de cláusulas puede resolverse",
        PositiveStrategy => "Al menos una cláusula debe tener todos sus literales positivos",
        NegativeStrategy => "Al menos una cláusula debe tener todos sus literales negativos",
        LinearStrategy => "Al menos una cláusula debe ser la última resolvente generada",
        UnitStrategy => "Al menos una cláusula debe ser unitaria (un solo literal)",
        InputStrategy => "Al menos una cláusula debe pertenecer al conjunto original"
    )
    
    return get(info, typeof(strategy), "Estrategia desconocida")
end

"""
    list_strategies()

Lista todas las estrategias disponibles con sus descripciones.
"""
function list_strategies()
    println("\n" * "="^80)
    println("ESTRATEGIAS DE RESOLUCIÓN DISPONIBLES")
    println("="^80)
    
    strategies = [
        NoStrategy(),
        PositiveStrategy(),
        NegativeStrategy(),
        LinearStrategy(),
        UnitStrategy(),
        InputStrategy()
    ]
    
    for (i, strategy) in enumerate(strategies)
        name = typeof(strategy)
        info = get_strategy_info(strategy)
        println("\n$i. $name")
        println("   $info")
    end
    
    println("\n" * "="^80)
end

end # module Resolution