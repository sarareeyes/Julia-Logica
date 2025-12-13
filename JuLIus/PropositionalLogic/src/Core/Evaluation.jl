"""
# Core.Evaluation - Sistema de Evaluación y Análisis de Fórmulas

Este submódulo implementa el sistema de evaluación de fórmulas proposicionales,
incluyendo valoraciones, análisis de componentes y funciones auxiliares.

## Contenido:
- Sistema de valoraciones (asignaciones de verdad)
- Evaluación composicional de fórmulas
- Análisis de variables y subfórmulas
- Funciones auxiliares para análisis estructural

## Componentes principales:
- `Valuation`: Tipo para asignaciones de verdad
- `evaluate`: Función de evaluación composicional
- `vars_of`: Extracción de variables
- `subformulas`: Análisis de estructura

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module Evaluation

using ..Types
import Base: show

export Valuation, evaluate, vars_of

# ==================== ANÁLISIS DE FÓRMULAS ====================

"""
    vars_of(f::FormulaPL) -> Set{Var_PL}

Obtiene todas las variables proposicionales que aparecen en una fórmula.

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
formula = (p & q) > r
variables = vars_of(formula)  # {p, q, r}
```

# Funcionamiento
Realiza un recorrido recursivo de la fórmula, recolectando todas las
variables proposicionales y devolviendo un conjunto (sin duplicados).

# Casos especiales
- Constantes lógicas (⊤, ⊥) no contribuyen variables
- Variables duplicadas se eliminan automáticamente por usar Set
"""
function vars_of(f::FormulaPL)
    if isa(f, Var_PL)
        return Set([f])
    elseif isa(f, Neg_PL)
        return vars_of(f.operand)
    elseif isa(f, Union{And_PL, Or_PL, Imp_PL, Iff_PL})
        return union(vars_of(f.left), vars_of(f.right))
    elseif isa(f, Union{Top_PL, Bottom_PL})
        return Set{Var_PL}()  # Las constantes no tienen variables
    else
        return Set{Var_PL}()
    end
end


# ================== VALORACIONES Y EVALUACIÓN DE FÓRMULAS ====================

"""
    Valuation = Dict{Var_PL, Bool}

Tipo alias para representar valoraciones (asignaciones de verdad).
Una valoración mapea cada variable proposicional a un valor booleano.

# Ejemplos
```julia
p, q = vars("p", "q")
val = Valuation(p => true, q => false)
```

# Interpretación matemática
Una valoración v: Var → {0,1} asigna valores de verdad a variables,
extendiendo la evaluación a fórmulas complejas de manera composicional.
"""
const Valuation = Dict{Var_PL, Bool}

"""
Función show personalizada para visualizar valoraciones de forma legible.
Muestra las asignaciones ordenadas alfabéticamente y usa 1/0 en lugar de true/false
para mayor claridad visual.

# Formato de salida
- Valoración vacía: ∅
- Valoración no vacía: {p = 1, q = 0, r = 1}
"""
function Base.show(io::IO, v::Valuation)
    if isempty(v)
        print(io, "∅")
    else
        # Ordenar las variables alfabéticamente para una salida consistente
        sorted_pairs = sort(collect(v), by = pair -> pair[1].name)
        assignments = ["$(var.name) = $(value ? "1" : "0")" for (var, value) in sorted_pairs]
        print(io, "{", join(assignments, ", "), "}")
    end
end

"""
    evaluate(f::FormulaPL, val::Valuation) -> Bool

Evalúa una fórmula proposicional bajo una valoración dada.

# Argumentos
- `f`: Fórmula proposicional a evaluar
- `val`: Valoración que asigna valores a las variables

# Retorna
`true` si la fórmula es verdadera bajo la valoración, `false` en caso contrario.

# Semántica implementada
- Variables: Valor asignado en la valoración (false por defecto si no está asignada)
- Constantes: ⊤ → true, ⊥ → false
- Negación: ¬φ → ¬v(φ)
- Conjunción: φ ∧ ψ → v(φ) ∧ v(ψ)
- Disyunción: φ ∨ ψ → v(φ) ∨ v(ψ)  
- Implicación: φ → ψ → ¬v(φ) ∨ v(ψ)
- Bicondicional: φ ↔ ψ → v(φ) ↔ v(ψ)

# Ejemplos
```julia
formula = p & q
val = Valuation(p => true, q => false)
result = evaluate(formula, val)  # false
```

# Notas
- Variables no asignadas en la valoración se consideran falsas por defecto
- La evaluación es compositional: se evalúan las subformulas y se combinan
"""
function evaluate(f::FormulaPL, val::Valuation)
    if isa(f, Var_PL)
        return get(val, f, false)  # false por defecto para variables no asignadas
    elseif isa(f, Top_PL)
        return true  # ⊤ siempre es verdadero
    elseif isa(f, Bottom_PL)
        return false  # ⊥ siempre es falso
    elseif isa(f, Neg_PL)
        return !evaluate(f.operand, val)
    elseif isa(f, And_PL)
        return evaluate(f.left, val) && evaluate(f.right, val)
    elseif isa(f, Or_PL)
        return evaluate(f.left, val) || evaluate(f.right, val)
    elseif isa(f, Imp_PL)
        return !evaluate(f.left, val) || evaluate(f.right, val)  # φ → ψ ≡ ¬φ ∨ ψ
    elseif isa(f, Iff_PL)
        return evaluate(f.left, val) == evaluate(f.right, val)   # φ ↔ ψ ≡ (φ → ψ) ∧ (ψ → φ)
    else
        return false  # Caso por defecto (no debería alcanzarse)
    end
end

"""
    (v::Valuation)(F) -> Bool

Permite usar una valoración como función aplicada a una fórmula.
Equivale a `evaluate(F, v)` pero con sintaxis más natural.

# Ejemplos
```julia
formula = p > q
val = Valuation(p => true, q => false)

# Ambas formas son equivalentes:
result1 = evaluate(formula, val)
result2 = val(formula)  # Sintaxis funcional más natural
```

# Ventajas
- Sintaxis más legible en algunos contextos
- Permite tratar valoraciones como funciones matemáticas v: FormulaPL → Bool
"""
function (v::Valuation)(F)
    return evaluate(F, v)
end

end # module Evaluation
