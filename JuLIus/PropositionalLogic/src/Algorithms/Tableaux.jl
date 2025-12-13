"""
# Algorithms.Tableaux - Tableros Semánticos (Método Analítico)

Este submódulo implementa el método de Tableros Semánticos para la verificación
de satisfactibilidad y validez de fórmulas proposicionales.

## Descripción del método:
Los Tableros Semánticos construyen un árbol de descomposición sistemática
de fórmulas, aplicando reglas que preservan la satisfactibilidad.

## Tipos de reglas:
- **Reglas α (no ramificantes)**: Descomponen fórmulas en subfórmulas que deben 
    ser todas verdaderas
- **Reglas β (ramificantes)**: Crean ramas alternativas donde al menos una debe 
    ser verdadera
- **Reglas de cierre**: Detectan contradicciones (p y ¬p en la misma rama)

## Aplicaciones:
- Verificación de satisfactibilidad (SAT)
- Verificación de validez (TAUT)
- Construcción de modelos
- Análisis de argumentos lógicos

## Ventajas:
- Intuición natural (árbol de casos)
- Facilidad de implementación
- Buena visualización del proceso de prueba

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module Tableaux

using ..Types
using ..Evaluation
using ..NormalForms
import Base: show

 export TableauNode, TS, TS_SAT, TS_TAUT, TS_solve, DNF_from_TS, CNF_from_TS,
        print_TS, plot_TS, save_TS_plot, has_contradiction, is_atomic, apply_α, 
        apply_β, extract_literals, truncate_string_safe

# ==================== ESTRUCTURA DEL TABLERO ====================

"""
    TableauNode

Tipo mutable para representar un nodo en el tablero semántico.

# Campos
- `formulas::Vector{FormulaPL}`: Fórmulas en este nodo
- `is_closed::Bool`: Indica si la rama está cerrada (contradicción)
- `children::Vector{TableauNode}`: Nodos hijos (ramas)
- `closure_reason::String`: Razón del cierre si está cerrado
- `depth::Int`: Profundidad en el árbol
- `branch_id::String`: Identificador de la rama
- `literals::Vector{FormulaPL}`: Conjunto de literales verificados en esta rama

# Estructura del árbol
- Nodos hoja: ramas abiertas (modelos) o cerradas (contradicciones)
- Nodos internos: puntos de ramificación
- Raíz: contiene las fórmulas iniciales
"""
mutable struct TableauNode
    formulas::Vector{FormulaPL}
    is_closed::Bool
    children::Vector{TableauNode}
    closure_reason::String
    depth::Int
    branch_id::String
    literals::Vector{FormulaPL}
end

"""
    TableauNode(Fs::Vector{FormulaPL}, depth::Int = 0, branch_id::String = "", literals::Vector{FormulaPL} = FormulaPL[]) -> TableauNode

Constructor para crear un nuevo nodo del tablero.

# Argumentos
- `Fs`: Vector de fórmulas en el nodo
- `depth`: Profundidad en el árbol (por defecto 0)
- `branch_id`: Identificador de rama (por defecto "")
- `literals`: Vector de literales verificados en esta rama (por defecto vacío)

# Inicialización
- `is_closed` se inicializa como false
- `children` como vector vacío
- `closure_reason` como string vacío
"""
function TableauNode(Fs::Vector{FormulaPL}, depth::Int = 0, branch_id::String = "", literals::Vector{FormulaPL} = FormulaPL[])
    return TableauNode(Fs, false, TableauNode[], "", depth, branch_id, copy(literals))
end

"""
Función show personalizada para visualizar nodos del tablero de forma jerárquica.
Muestra la estructura con indentación apropiada y marca el estado de cierre.
"""
function Base.show(io::IO, node::TableauNode)
    indent = "  " ^ node.depth
    println(io, "$(indent)$(node.branch_id){")
    for F in node.formulas
        println(io, "$(indent)  $F")
    end
    if node.is_closed
        println(io, "$(indent)  ⊗ CERRADO: $(node.closure_reason)")
    end
    println(io, "$(indent)}")
end

# ==================== ANÁLISIS DE FÓRMULAS ====================

"""
    extract_literals(Fs::Vector{FormulaPL}) -> Vector{FormulaPL}

Extrae todos los literales (variables y negaciones de variables) de un conjunto de fórmulas.

# Retorna
Vector con todos los literales encontrados en las fórmulas.

# Ejemplos
```julia
p, q = vars("p", "q")
formulas = [p, !q, p & q]
literals = extract_literals(formulas)
# [p, ¬q]
```
"""
function extract_literals(Fs::Vector{FormulaPL})
    literals = FormulaPL[]
    for F in Fs
        if is_atomic(F)
            push!(literals, F)
        end
    end
    return literals
end

"""
    has_contradiction(Fs::Vector{FormulaPL}) -> (Bool, String)

Verifica si hay contradicción en un conjunto de fórmulas.

# Definición
Una contradicción ocurre cuando aparecen p y ¬p para la misma variable p.

# Retorna
Tupla (tiene_contradiccion, razon) donde:
- `tiene_contradiccion`: true si hay contradicción
- `razon`: descripción de la contradicción encontrada

# Algoritmo
1. Separa átomos positivos y negativos
2. Busca intersección entre ambos conjuntos
3. Reporta la primera contradicción encontrada

# Ejemplos
```julia
p = vars("p")[1]
formulas = [p, !p]
tiene_contr, razon = has_contradiction(formulas)
# (true, "p y ¬p")
```
"""
function has_contradiction(Fs::Vector{FormulaPL})
    # Convertir todas las fórmulas a una representación normalizada
    pos_atoms = Set{Var_PL}()
    neg_atoms = Set{Var_PL}()
    
    for F in Fs
        if isa(F, Var_PL)
            push!(pos_atoms, F)
        elseif isa(F, Neg_PL) && isa(F.operand, Var_PL)
            push!(neg_atoms, F.operand)
        end
    end
    
    # Verificar si hay contradicción directa
    contradiction = intersect(pos_atoms, neg_atoms)
    if !isempty(contradiction)
        return true, "$(first(contradiction)) y ¬$(first(contradiction))"
    end
    
    return false, ""
end

"""
    is_atomic(f::FormulaPL) -> Bool

Verifica si una fórmula es atómica (literal). Usamos la nomenclatura habitual 
del algoritmo, pero podríamos haberlo llamado `is_literal`.

# Definición
Una fórmula atómica es:
- Una variable proposicional: p
- La negación de una variable: ¬p

# Ejemplos
```julia
p = vars("p")[1]
is_atomic(p)        # true
is_atomic(!p)       # true
is_atomic(p & q)    # false
```

# Uso en tableros
Los literales (como fórmulas) son casos base que no requieren más 
descomposición.
"""
function is_atomic(f::FormulaPL)
    return isa(f, Var_PL) || (isa(f, Neg_PL) && isa(f.operand, Var_PL))
end

# ==================== REGLAS DE DESCOMPOSICIÓN ====================

"""
    apply_α(Fs::Vector{FormulaPL}) -> (Vector{FormulaPL}, Bool)

Aplica reglas α (no ramificantes) a un conjunto de fórmulas.

# Reglas α implementadas:
- **Conjunción**: A ∧ B => A, B
- **De Morgan**: ¬(A ∨ B) => ¬A, ¬B
- **Negación de implicación**: ¬(A → B) => A, ¬B
- **Doble negación**: ¬¬A => A

# Características:
- Preservan satisfactibilidad: Fs satisfactible ⇔ apply_α(Fs) satisfactible
- No ramificantes: una sola nueva colección de fórmulas
- Simplifican fórmulas complejas
- Se aplican a todas las fórmulas α en el conjunto

# Retorna
Tupla (nuevas_formulas, regla_aplicada) donde:
- `nuevas_formulas`: resultado de aplicar las reglas
- `regla_aplicada`: true si se aplicó alguna regla de tipo α

# Ejemplos
```julia
p, q = vars("p", "q")
formulas = [p & q]
nuevas, aplicada = apply_α(formulas)
# nuevas = [p, q], aplicada = true
```
"""
function apply_α(Fs::Vector{FormulaPL})
    new_Fs = FormulaPL[]
    applied_rule = false
    
    for F in Fs
        if isa(F, And_PL)
            # α-regla para conjunción: A ∧ B ↪ A, B
            push!(new_Fs, F.left)
            push!(new_Fs, F.right)
            applied_rule = true
        elseif isa(F, Neg_PL) && isa(F.operand, Or_PL)
            # α-regla para ¬(A ∨ B) ↪ ¬A, ¬B (De Morgan)
            push!(new_Fs, !(F.operand.left))
            push!(new_Fs, !(F.operand.right))
            applied_rule = true
        elseif isa(F, Neg_PL) && isa(F.operand, Imp_PL)
            # α-regla para ¬(A → B) ↪ A, ¬B
            push!(new_Fs, F.operand.left)
            push!(new_Fs, !(F.operand.right))
            applied_rule = true
        elseif isa(F, Neg_PL) && isa(F.operand, Neg_PL)
            # Eliminación de doble negación: ¬¬A ↪ A
            push!(new_Fs, F.operand.operand)
            applied_rule = true
        else
            # Mantener fórmulas que no son α-reglas
            push!(new_Fs, F)
        end
    end
    
    return new_Fs, applied_rule
end

"""
    apply_β(Fs::Vector{FormulaPL}) -> (Bool, Vector{FormulaPL}, Vector{FormulaPL}, String)

Encuentra y aplica la primera regla β (ramificante) aplicable.

# Reglas β implementadas:
- **Disyunción**: A ∨ B => A | B
- **De Morgan**: ¬(A ∧ B) => ¬A | ¬B
- **Implicación**: A → B => ¬A | B
- **Bicondicional**: A ↔ B => (A ∧ B) | (¬A ∧ ¬B)
- **Negación de bicondicional**: ¬(A ↔ B) => (A ∧ ¬B) | (¬A ∧ B)

# Características:
- Ramificantes: crean dos ramas alternativas
- Al menos una rama debe ser satisfactible para que el conjunto original lo sea
- Se aplica solo a la primera fórmula β encontrada (podría pensarse en una 
    estrategia alternativa de selección)

# Retorna
Tupla (regla_encontrada, rama_izquierda, rama_derecha, descripcion) donde:
- `regla_encontrada`: true si se encontró una regla β aplicable
- `rama_izquierda`: fórmulas para la primera rama
- `rama_derecha`: fórmulas para la segunda rama  
- `descripcion`: descripción de la regla β aplicada

# Ejemplos
```julia
p, q = vars("p", "q")
formulas = [p | q]
encontrada, izq, der, desc = apply_β(formulas)
# encontrada = true, izq = [p], der = [q], desc = "p ∨ q"
```
"""
function apply_β(Fs::Vector{FormulaPL})
    for (i, F) in enumerate(Fs)
        remaining = [Fs[j] for j in 1:length(Fs) if j != i]
        
        if isa(F, Or_PL)
            # β-regla para disyunción: A ∨ B → A | B
            left_branch = vcat(remaining, [F.left])
            right_branch = vcat(remaining, [F.right])
            return true, left_branch, right_branch, "$(F.left) ∨ $(F.right)"
            
        elseif isa(F, Neg_PL) && isa(F.operand, And_PL)
            # β-regla para ¬(A ∧ B) → ¬A | ¬B (De Morgan)
            left_branch = vcat(remaining, [!(F.operand.left)])
            right_branch = vcat(remaining, [!(F.operand.right)])
            return true, left_branch, right_branch, "¬($(F.operand.left) ∧ $(F.operand.right))"
            
        elseif isa(F, Imp_PL)
            # β-regla para implicación: A → B ≡ ¬A ∨ B
            left_branch = vcat(remaining, [!(F.left)])
            right_branch = vcat(remaining, [F.right])
            return true, left_branch, right_branch, "$(F.left) → $(F.right)"
            
        elseif isa(F, Iff_PL)
            # β-regla para bicondicional: A ↔ B → (A ∧ B) | (¬A ∧ ¬B)
            left_branch = vcat(remaining, [F.left, F.right])
            right_branch = vcat(remaining, [!(F.left), !(F.right)])
            return true, left_branch, right_branch, "$(F.left) ↔ $(F.right)"
            
        elseif isa(F, Neg_PL) && isa(F.operand, Iff_PL)
            # β-regla para ¬(A ↔ B) → (A ∧ ¬B) | (¬A ∧ B)
            bic = F.operand
            left_branch = vcat(remaining, [bic.left, !(bic.right)])
            right_branch = vcat(remaining, [!(bic.left), bic.right])
            return true, left_branch, right_branch, "¬($(bic.left) ↔ $(bic.right))"
        end
    end
    return false, FormulaPL[], FormulaPL[], ""
end

# ==================== CONSTRUCCIÓN DEL TABLERO ====================

"""
    TS(input_Fs::Vector{T}, depth::Int = 0, branch_id::String = "1", parent_literals::Vector{FormulaPL} = FormulaPL[]) -> (TableauNode, Vector{Dict{String, Any}}) where T

Construye recursivamente un tablero semántico completo manteniendo los literales de cada rama.

# Algoritmo:
1. **Verificación inicial**: Buscar contradicciones inmediatas
2. **Aplicación de reglas α**: Repetir un número máximo de veces
3. **Verificación de cierre**: Detectar contradicciones después de α-reglas
4. **Caso base**: Si todas son literales, rama completa
5. **Aplicación de reglas β**: Crear ramificación
6. **Recursión**: Construir subrableros para cada rama
7. **Propagación de cierre**: Cerrar nodo si todas las ramas se cierran
8. **Extracción de modelos**: Recopilar literales de ramas abiertas

# Argumentos
- `input_Fs`: Fórmulas iniciales (pueden ser de cualquier tipo convertible)
- `depth`: Profundidad actual en el árbol

# Retorna
Tupla (nodo_raiz, modelos) donde:
- `nodo_raiz`: Nodo raíz del tablero construido
- `modelos`: Vector de diccionarios con información de ramas abiertas

# Características
- **Terminación**: Garantizada para lógica proposicional
- **Completitud**: Encuentra todos los modelos
- **Corrección**: Cierre indica insatisfactibilidad
"""
function TS(input_Fs::Vector{T}, depth::Int = 0, branch_id::String = "1", parent_literals::Vector{FormulaPL} = FormulaPL[]) where T
    # Convertir el input a Vector{FormulaPL} para asegurar compatibilidad de tipos
    Fs = FormulaPL[f for f in input_Fs]
    
    # Extraer literales actuales
    current_literals = extract_literals(Fs)

    node = TableauNode(Fs, depth, branch_id, current_literals)
    
    # Vector para almacenar modelos de ramas abiertas
    models = Dict{String, Any}[]
    
    # Verificar contradicción inicial
    has_contr, reason = has_contradiction(Fs)
    if has_contr
        node.is_closed = true
        node.closure_reason = reason
        return node, models
    end
    
    # Aplicar reglas α repetidamente hasta punto fijo
    current_Fs = copy(Fs)
    max_iterations = 50  # Prevenir bucles infinitos
    iteration = 0
    
    while iteration < max_iterations
        iteration += 1
        new_Fs, applied = apply_α(current_Fs)
        
        if !applied
            break  # Punto fijo alcanzado
        end
        
        current_Fs = new_Fs
        
        # Verificar contradicción después de α-reglas
        has_contr, reason = has_contradiction(current_Fs)
        if has_contr
            node.formulas = current_Fs
            node.is_closed = true
            node.closure_reason = reason
            return node, models
        end
    end
    
    # Actualizar nodo con fórmulas procesadas por α-reglas
    node.formulas = current_Fs
    
    # Actualizar literales después del procesamiento α
    node.literals = extract_literals(current_Fs)
    
    # Verificar si todas son literales (caso base)
    if all(is_atomic, current_Fs)
        # Rama abierta - todas son literales y no hay contradicción
        # Esta rama representa un modelo potencial
        model = Dict{String, Any}(
            "branch_id" => branch_id,
            "literals" => node.literals
        )
        push!(models, model)
        return node, models
    end
    
    # Aplicar reglas β (ramificantes)
    found_beta, left_branch, right_branch, beta_reason = apply_β(current_Fs)
    
    if found_beta
        # Crear ramas hijas con llamada recursiva
        left_child, left_models = TS(left_branch, depth + 1, branch_id * ".1", node.literals)
        right_child, right_models = TS(right_branch, depth + 1, branch_id * ".2", node.literals)
        
        node.children = [left_child, right_child]
        
        # Combinar modelos de ambas ramas
        models = vcat(left_models, right_models)
        
        # Cerrar nodo si ambas ramas se cierran
        # El nodo está cerrado ssi todas sus ramas están cerradas
        node.is_closed = left_child.is_closed && right_child.is_closed
        if node.is_closed
            node.closure_reason = "Ambas ramas se cierran"
        end
    end
    
    return node, models
end

"""
    TS(f::FormulaPL) -> TableauNode

Función de conveniencia para crear un tablero desde una sola fórmula.

# Ejemplos
```julia
p, q = vars("p", "q")
formula = (p & q) | (!p & !q)
tablero = TS_from_formula(formula)
```
"""
function TS(f::FormulaPL)
    return TS([f])
end

# ==================== FUNCIONES AUXILIARES PARA MODELOS ====================

# """
#     get_models(tableau_node::TableauNode) -> Vector{Dict{String, Any}}

# Extrae todos los modelos (ramas abiertas) de un tablero semántico construido.

# # Argumentos
# - `tableau_node`: Nodo raíz del tablero construido

# # Retorna
# Vector de diccionarios, cada uno representando un modelo con:
# - `branch_id`: Identificador de la rama
# - `literals`: Vector de literales que forman el modelo
# - `is_model`: Siempre true para ramas abiertas
# - `depth`: Profundidad de la rama

# # Ejemplo
# ```julia
# p, q = vars("p", "q")
# tableau, models = build_TS([p | q])
# models_only = get_models(tableau)
# ```
# """
# function get_models(node::TableauNode)
#     models = Dict{String, Any}[]
    
#    if !node.is_closed && isempty(node.children)
#       # Es una rama abierta (hoja no cerrada)
#       model = Dict{String, Any}(
#             "branch_id" => node.branch_id,
#             "literals" => node.literals
#       )
#       push!(models, model)
#    else
#       # Recursión en nodos hijos
#       for child in node.children
#             collect_models(child)
#       end
#    end
    
#     return models
# end

# ==================== FUNCIONES DE VERIFICACIÓN ====================

"""
    TS_SAT(f::FormulaPL) -> Bool

Verifica satisfactibilidad usando tableros semánticos.

# Algoritmo
1. Construye tablero para f
2. f es satisfactible ⟺ el tablero tiene al menos una rama abierta

# Interpretación
- Rama abierta: modelo encontrado (conjunto de literales consistente)
- Todas las ramas cerradas: fórmula insatisfactible

# Ejemplos
```julia
p, q = vars("p", "q")
formula = p & !p  # Contradicción
result = TS_SAT(formula)  # false

formula2 = p | !p  # Tautología  
result2 = TS_SAT(formula2)  # true
```
"""
function TS_SAT(f::FormulaPL)
    println("Construyendo tablero semántico para: $f")
    println("=" ^ (37 + length(string(f))))
    tableau, models = TS(f)
    ms = [⋀(model["literals"]) for model in models]
    print_TS(tableau)
    
    satisfiable = !tableau.is_closed
    println("\nResultado: $(satisfiable ? "SATISFACTIBLE" : "INSATISFACTIBLE")")
    
    return satisfiable, ms
end

"""
    TS_TAUT(f::FormulaPL) -> Bool

Verifica validez (tautología) usando tableros semánticos.

# Algoritmo
1. Construye tablero para ¬f
2. f es tautología ↔ ¬f es insatisfactible ↔ tablero para ¬f está completamente cerrado

# Método indirecto
Este es el método estándar: verificar que la negación es insatisfactible.

# Ejemplos
```julia
p = vars("p")[1]
tautologia = p | !p
result = TS_TAUT(tautologia)  # true

contingencia = p
result2 = TS_TAUT(contingencia)  # false
```
"""
function TS_TAUT(f::FormulaPL)
    println("Verificando validez de: $f")
    println("Construyendo tablero para ¬($f)")
    println("=" ^ (37 + length(string(f))))
    
    # Una fórmula es Tautología si ¬f es insatisfactible
    negated_formula = Neg_PL(f)
    tableau,_ = TS(negated_formula)
    print_TS(tableau)
    
    valid = tableau.is_closed
    println("\nResultado: $(valid ? "TAUTOLOGÍA" : "NO TAUTOLOGÍA")")
    
    return valid
end

"""
    TS_solve(f::FormulaPL) -> (Bool, Bool)

Análisis completo de una fórmula usando tableros semánticos.

# Análisis realizado:
1. Verificación de satisfactibilidad
2. Verificación de validez (tautología)
3. Clasificación semántica completa

# Retorna
Tupla (satisfactible, tautologia) con los resultados del análisis.

# Clasificación semántica:
- **Tautología**: siempre verdadera (satisfactible = true, tautologia = true)
- **Contradicción**: siempre falsa (satisfactible = false, tautologia = false)  
- **Contingencia**: a veces verdadera (satisfactible = true, tautologia = false)

# Ejemplos
```julia
p, q = vars("p", "q")
formula = (p & q) | (!p & !q)  # Bicondicional
satisf, valid = TS_solve(formula)
```
"""
function TS_solve(f::FormulaPL)
    println("=== ANÁLISIS COMPLETO CON TABLEROS SEMÁNTICOS ===")
    println("Fórmula: $f")
    println()
    
    # Verificar satisfactibilidad
    println("1. VERIFICACIÓN DE SATISFACTIBILIDAD:")
    satisfiable, models = TS_SAT(f)
    println()
    
    # Verificar validez
    println("2. VERIFICACIÓN DE VALIDEZ:")
    valid = TS_TAUT(f)
    println()
    
    # Resumen y clasificación
    println("=== RESUMEN ===")
    println("Fórmula: $f")
    println("Satisfactible: $(satisfiable ? "SÍ" : "NO")")
    println("Modelos encontrados:")
    if satisfiable
        for (i, model) in enumerate(models)
            println("  Modelo $(i): $(model)")
        end
    end

    println("Tautología: $(valid ? "SÍ" : "NO")")
    if satisfiable && !valid
        println("Clasificación: CONTINGENTE")
    elseif !satisfiable && !valid
        println("Clasificación: CONTRADICCIÓN")
    elseif satisfiable && valid
        println("Clasificación: TAUTOLOGÍA")
    end
    
    return satisfiable, valid
end

# ==================== CONVERSIÓN A FND/FNC ====================

"""
    FND_from_TS(f::FormulaPL) -> FormulaPL
Construye la Forma Normal Disyuntiva (FND) de una fórmula usando tableros semánticos.
# Algoritmo
1. Construye el tablero para f
2. Extrae los modelos (ramas abiertas)
3. Cada modelo se convierte en una conjunción de sus literales
4. La FND es la disyunción de todas estas conjunciones

Transformamos los literales de cada modelo en un conjunto para eliminar repetidos.

"""

function DNF_from_TS(f::FormulaPL)
    _, m = TS([f])
    ms = [⋀(sort(collect(Set(mod["literals"])), by = varl)) for mod in m]
    return ⋁(ms)
end

"""
    FNC_from_TS(f::FormulaPL) -> FormulaPL
Construye la Forma Normal Conjuntiva (FNC) de una fórmula usando tableros semánticos.
# Algoritmo
1. Construye el tablero para ¬f
2. Extrae los modelos (ramas abiertas) de ¬f
3. Cada modelo se convierte en una conjunción de sus literales
4. La FNC es la disyunción de todas estas conjunciones

Transformamos los literales de cada modelo en un conjunto para eliminar repetidos.
"""

function CNF_from_TS(f::FormulaPL)
    _, ms = TS([-f])
    ms_clean = [sort(collect(Set(m["literals"])), by = varl) for m in ms]
    ms = [⋁([move_negation_in(-l) for l in m]) for m in ms_clean]
    return ⋀(ms)
end

# Función auxiliar para poder ordenar literales alfabéticamente con sort-by
function varl(l::Union{Var_PL, Neg_PL})
    if isa(l, Var_PL)
        return l
    else
        return l.operand
    end
end

# ==================== VISUALIZACIÓN ====================

"""
    print_TS(node::TableauNode, io::IO = stdout)

Imprime un tablero semántico de forma jerárquica.

# Formato de salida:
- Indentación proporcional a la profundidad
- Identificación de ramas por ID
- Marcado claro de ramas cerradas y abiertas
- Razones de cierre cuando aplique
- Literales verificados en cada rama

# Ejemplo de salida:
```
Rama 1:
  p ∨ q
  ¬p
  Literales: [¬p]
  Rama 1.1:
    p
    ¬p
    Literales: [¬p, p]
    ⊗ CERRADA: p y ¬p
  Rama 1.2:
    q
    ¬p
    Literales: [¬p, q]
    ✓ ABIERTA (satisfactible)
```
"""
function print_TS(node::TableauNode, io::IO = stdout)
    indent = "  " ^ node.depth
    
    println(io, "$(indent)Rama $(node.branch_id):")
    for F in node.formulas
        println(io, "$(indent)  $F")
    end
    
    # Mostrar literales si hay alguno
    if !isempty(node.literals)
        println(io, "$(indent)  Literales: $(node.literals)")
    end
    
    if node.is_closed
        println(io, "$(indent)  ⊗ CERRADA: $(node.closure_reason)")
    elseif isempty(node.children)
        println(io, "$(indent)  ✓ ABIERTA (satisfactible)")
    end
    
    # Imprimir recursivamente todos los hijos
    for child in node.children
        print_TS(child, io)
    end
end

function print_TS(tableau_result::Tuple{TableauNode, Vector{Dict{String, Any}}}; kwargs...)
    node, models = tableau_result
    return print_TS(node; kwargs...)
end

# ==================== VISUALIZACIÓN GRÁFICA ====================

"""
    plot_TS(node::TableauNode; kwargs...) -> Plot

Genera una visualización gráfica del tablero semántico como un árbol usando Plots.jl.

# Argumentos
- `node`: Nodo raíz del tablero semántico
- `kwargs...`: Argumentos adicionales para personalizar el plot

# Opciones de personalización
- `title`: Título del gráfico (por defecto "Tablero Semántico")
- `node_size`: Tamaño de los nodos (por defecto 8)
- `font_size`: Tamaño de fuente (por defecto 8)
- `figure_size`: Tamaño de la figura (por defecto (800, 600))

# Retorna
Objeto Plot de Plots.jl que puede ser mostrado o guardado.

# Ejemplos
```julia
using Plots
p, q = vars("p", "q")
formula = (p & q) | (!p & !q)
tableau, models = TS(formula)
plot_TS(tableau, title="Tablero para (p∧q)∨(¬p∧¬q)")
```

# Características visuales
- **Nodos cerrados**: Cajas rojas con branch_id, fórmulas debajo y estado "⊗"
- **Nodos abiertos**: Cajas verdes con branch_id, fórmulas debajo y estado "✓"  
- **Nodos internos**: Cajas azules con branch_id y fórmulas debajo
- **Aristas**: Líneas conectando padres e hijos
- **Layout**: branch_id en caja + información adicional debajo

# Dependencias
Requiere que Plots.jl esté cargado: `using Plots` antes de llamar esta función.
"""
function plot_TS(node::TableauNode; 
                title::String = "Tablero Semántico",
                node_size::Int = 10,
                font_size::Int = 12,
                figure_size::Tuple{Int, Int} = (1200, 1200))
    
    # Verificar que Plots esté disponible
    if !isdefined(Main, :Plots)
        error("Esta función requiere Plots.jl. Ejecute 'using Plots' primero.")
    end
    
    # Recopilar información del árbol
    positions, branch_ids, additional_info, colors, edges = _analyze_tree_structure(node)
    
    # Crear el gráfico
    plt = Main.Plots.plot(
        size = figure_size,
        title = title,
        titlefontsize = font_size + 6,
        legend = :topright,
        framestyle = :none,
        aspect_ratio = :equal
    )
    
    # Dibujar aristas
    for (parent_pos, child_pos) in edges
        Main.Plots.plot!(plt, 
            [parent_pos[1], child_pos[1]], 
            [parent_pos[2], child_pos[2]], 
            color = :black, 
            linewidth = 1, 
            alpha = 0.6,
            label = ""
        )
    end
    
    # Calcular límites expandidos para incluir las cajas
    x_coords = [pos[1] for pos in positions]
    y_coords = [pos[2] for pos in positions]
    
    min_x, max_x = extrema(x_coords)
    min_y, max_y = extrema(y_coords)
    
    # Expandir los límites para dar espacio a las cajas y su información adicional
    margin_x = 1.0
    margin_y = 1.5  # Más margen vertical para la información debajo de las cajas
    
    Main.Plots.xlims!(plt, min_x - margin_x, max_x + margin_x)
    Main.Plots.ylims!(plt, min_y - margin_y, max_y + 0.5)
    
    # Dibujar nodos como cajas en lugar de círculos
    for (i, (pos, branch_id, info, color)) in enumerate(zip(positions, branch_ids, additional_info, colors))
        _draw_node_box!(plt, pos, branch_id, info, color, font_size)
    end
    
    # Añadir leyenda manual (usando puntos pequeños para la leyenda)
    Main.Plots.scatter!(plt, [NaN], [NaN], color = :red, markersize = 6, 
                       label = "Rama cerrada")
    Main.Plots.scatter!(plt, [NaN], [NaN], color = :green, markersize = 6, 
                       label = "Rama abierta") 
    Main.Plots.scatter!(plt, [NaN], [NaN], color = :lightblue, markersize = 6, 
                       label = "Nodo interno")
    
    return plt
end

"""
    plot_TS(tableau_result::Tuple{TableauNode, Vector{Dict}}; kwargs...) -> Plot

Versión de conveniencia que acepta el resultado directo de TS().

# Argumentos
- `tableau_result`: Tupla devuelta por TS(formula)
- `kwargs...`: Argumentos adicionales para personalizar el plot

# Ejemplos
```julia
using Plots
p, q = vars("p", "q")
formula = (p & q) | (!p & !q)
tableau_result = TS(formula)  # Devuelve (TableauNode, Vector{Dict})
plot_TS(tableau_result, title="Tablero para (p∧q)∨(¬p∧¬q)")
```
"""
function plot_TS(tableau_result::Tuple{TableauNode, Vector{Dict{String, Any}}}; kwargs...)
    node, models = tableau_result
    return plot_TS(node; kwargs...)
end

"""
    _analyze_tree_structure(node::TableauNode) -> (Vector{Tuple{Float64, Float64}}, Vector{String}, Vector{String}, Vector{Symbol}, Vector{Tuple{Tuple{Float64, Float64}, Tuple{Float64, Float64}}})

Función auxiliar que analiza la estructura del tablero y calcula posiciones, etiquetas, colores y conexiones.

# Algoritmo de posicionamiento
1. **Distribución horizontal**: Usa un algoritmo de separación de subtrees
2. **Distribución vertical**: Basada en la profundidad del nodo
3. **Balanceamiento**: Centra subtrees automáticamente

# Retorna
Tupla con:
- `positions`: Vector de coordenadas (x, y) para cada nodo
- `branch_ids`: Vector de branch_ids para las cajas
- `additional_info`: Vector de información adicional para debajo de las cajas
- `colors`: Vector de colores para cada nodo
- `edges`: Vector de tuplas de posiciones para dibujar aristas
"""
function _analyze_tree_structure(node::TableauNode)
    positions = Tuple{Float64, Float64}[]
    branch_ids = String[]
    additional_info = String[]
    colors = Symbol[]
    edges = Tuple{Tuple{Float64, Float64}, Tuple{Float64, Float64}}[]
    
    # Calcular posiciones usando un layout de árbol
    node_positions = Dict{TableauNode, Tuple{Float64, Float64}}()
    _calculate_positions!(node, node_positions, 0.0, 0.0, 10.0)
    
    # Recopilar información de todos los nodos
    _collect_node_info!(node, node_positions, positions, branch_ids, additional_info, colors, edges)
    
    return positions, branch_ids, additional_info, colors, edges
end

"""
    _calculate_positions!(node::TableauNode, positions::Dict, x::Float64, y::Float64, width::Float64)

Calcula recursivamente las posiciones de todos los nodos en el árbol.
"""
function _calculate_positions!(node::TableauNode, positions::Dict, x::Float64, y::Float64, width::Float64)
    positions[node] = (x, y)
    
    if !isempty(node.children)
        num_children = length(node.children)
        child_width = width / num_children
        start_x = x - width/2 + child_width/2
        
        for (i, child) in enumerate(node.children)
            child_x = start_x + (i-1) * child_width
            child_y = y - 2.5  # Más separación vertical para acomodar información adicional
            _calculate_positions!(child, positions, child_x, child_y, child_width)
        end
    end
end

"""
    _collect_node_info!(node::TableauNode, node_positions::Dict, positions::Vector, branch_ids::Vector, additional_info::Vector, colors::Vector, edges::Vector)

Recopila recursivamente la información de visualización de todos los nodos.
"""
function _collect_node_info!(node::TableauNode, node_positions::Dict, positions::Vector, branch_ids::Vector, additional_info::Vector, colors::Vector, edges::Vector)
    # Información del nodo actual
    pos = node_positions[node]
    push!(positions, pos)
    
    # Branch ID para la caja
    push!(branch_ids, node.branch_id)
    
    # Información adicional para debajo de la caja
    info_lines = String[]
    
    # Recopilar fórmulas para mostrar debajo de la caja
    if !isempty(node.formulas)
        max_formulas_to_show = isempty(node.children) ? 4 : 3
        
        for (i, formula) in enumerate(node.formulas)
            if i > max_formulas_to_show
                push!(info_lines, "... ($(length(node.formulas) - max_formulas_to_show) más)")
                break
            end
            
            formula_str = string(formula)
            max_length = 20
            
            if length(formula_str) > max_length
                formula_str = truncate_string_safe(formula_str, 17) * "..."
            end
            push!(info_lines, formula_str)
        end
    end
    
    # Para nodos finales (hojas), añadir estado
    if isempty(node.children)
        if node.is_closed
            push!(info_lines, "⊗ ($(node.closure_reason))")
        else
            push!(info_lines, "✓ SAT")
        end
    end
    
    # Guardar información adicional como string
    info_text = isempty(info_lines) ? "" : join(info_lines, "\n")
    push!(additional_info, info_text)
    
    # Determinar color según estado del nodo
    if node.is_closed
        push!(colors, :red)           # Nodo cerrado
    elseif isempty(node.children)
        push!(colors, :green)         # Hoja abierta (satisfactible)
    else
        push!(colors, :lightblue)     # Nodo interno
    end
    
    # Procesar hijos y crear aristas
    for child in node.children
        child_pos = node_positions[child]
        push!(edges, (pos, child_pos))
        _collect_node_info!(child, node_positions, positions, branch_ids, additional_info, colors, edges)
    end
end

"""
    _draw_node_box!(plt, pos, branch_id, additional_info, color, font_size)

Dibuja una caja rectangular para representar un nodo del tablero.
"""
function _draw_node_box!(plt, pos, branch_id, additional_info, color, font_size)
    x, y = pos
    box_width = 0.8
    box_height = 0.4
    
    # Definir los vértices del rectángulo
    rect_x = [x - box_width/2, x + box_width/2, x + box_width/2, x - box_width/2, x - box_width/2]
    rect_y = [y - box_height/2, y - box_height/2, y + box_height/2, y + box_height/2, y - box_height/2]
    
    # Dibujar el rectángulo
    Main.Plots.plot!(plt, rect_x, rect_y, 
                    fillcolor = color, 
                    fillalpha = 1.0,        # Completamente opaco
                    linecolor = :black, 
                    linewidth = 2,
                    seriestype = :shape,    # Asegurar que es una forma rellena
                    label = "")
    
    # Añadir el branch_id centrado en la caja
    Main.Plots.annotate!(plt, x, y, Main.Plots.text(branch_id, font_size, :center, :black))
    
    # Añadir información adicional debajo de la caja si existe
    if !isempty(additional_info)
        # Calcular posición debajo de la caja
        num_lines = count(c -> c == '\n', additional_info) + 1
        offset_y = box_height/2 + 0.4 #+ (num_lines * 0.15)
        Main.Plots.annotate!(plt, x, y - offset_y, 
                           Main.Plots.text(additional_info, font_size-1, :center, :black))
    end
end

"""
    truncate_string_safe(s::String, max_chars::Int) -> String

Trunca un string de forma segura respetando los caracteres Unicode.

# Argumentos
- `s`: String a truncar
- `max_chars`: Número máximo de caracteres (no bytes)

# Retorna
String truncado que no excede max_chars caracteres

# Características
- Respeta los límites de caracteres Unicode
- No corta en medio de un carácter multibyte
- Maneja correctamente símbolos lógicos como ∨, ∧, ¬, etc.
"""
function truncate_string_safe(s::String, max_chars::Int)
    if length(s) <= max_chars
        return s
    end
    
    # Usar first() que es seguro con Unicode
    return first(s, max_chars)
end

"""
    save_TS_plot(node::TableauNode, filename::String; kwargs...)

Guarda la visualización del tablero semántico en un archivo.

# Argumentos
- `node`: Nodo raíz del tablero
- `filename`: Nombre del archivo (extensión determina formato: .png, .pdf, .svg, etc.)
- `kwargs...`: Argumentos adicionales pasados a plot_TS

# Ejemplos
```julia
tableau, models = TS(formula)
save_TS_plot(tableau, "mi_tablero.png", title="Mi Tablero")
save_TS_plot(tableau, "tablero.pdf", figure_size=(1200, 800))
```
"""
function save_TS_plot(node::TableauNode, filename::String; kwargs...)
    plt = plot_TS(node; kwargs...)
    Main.Plots.savefig(plt, filename)
    println("Tablero guardado en: $filename")
    return plt
end

"""
    save_TS_plot(tableau_result::Tuple{TableauNode, Vector{Dict}}, filename::String; kwargs...)

Versión de conveniencia que acepta el resultado directo de TS().

# Argumentos
- `tableau_result`: Tupla devuelta por TS(formula)
- `filename`: Nombre del archivo
- `kwargs...`: Argumentos adicionales pasados a plot_TS

# Ejemplos
```julia
tableau_result = TS(formula)
save_TS_plot(tableau_result, "mi_tablero.png")
```
"""
function save_TS_plot(tableau_result::Tuple{TableauNode, Vector{Dict{String, Any}}}, filename::String; kwargs...)
    node, models = tableau_result
    return save_TS_plot(node, filename; kwargs...)
end

end # module Tableaux
