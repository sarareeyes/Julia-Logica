"""
# Core.Types - Tipos Base del Sistema de Lógica Proposicional

Este submódulo define los tipos fundamentales para representar fórmulas de 
Lógica Proposicional, incluyendo la jerarquía de tipos, operadores sobrecargados 
y funciones auxiliares básicas.

## Contenido:
- Jerarquía de tipos para fórmulas proposicionales
- Sobrecarga de operadores para sintaxis natural
- Funciones auxiliares para construcción de fórmulas
- Constantes lógicas básicas

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module Types

export FormulaPL, Var_PL, Neg_PL, And_PL, Or_PL, Imp_PL, Iff_PL, Top_PL, Bottom_PL
export ⊤, ⊥, ⋀, ⋁, vars, @formula

# ==================== TIPOS DE FÓRMULAS PROPOSICIONALES ====================

"""
Jerarquía de tipos para representar fórmulas de la lógica proposicional.
Utiliza un diseño jerárquico con tipos abstractos para permitir dispatch 
múltiple y extensibilidad futura.
"""

# Tipo abstracto base para todas las fórmulas proposicionales
abstract type FormulaPL end

# ==================== TIPOS CONCRETOS ====================

"""
    Var_PL(name::String) <: FormulaPL

Representa una variable proposicional.

# Ejemplos
```julia
p = Var_PL("p")
```
"""
struct Var_PL <: FormulaPL
    name::String        # Nombre de la variable como cadena de texto
end

"""
    Neg_PL(operand::FormulaPL) <: FormulaPL

Representa la negación de una fórmula (¬φ).

# Ejemplos
```julia
Neg_PL(p & q)  # ¬(p ∧ q)
```
"""
struct Neg_PL <: FormulaPL
    operand::FormulaPL
end

"""
    And_PL(left::FormulaPL, right::FormulaPL) <: FormulaPL

Representa la conjunción de dos fórmulas (φ ∧ ψ).

# Ejemplos
```julia
And_PL(p, q)  # p ∧ q
```
"""
struct And_PL <: FormulaPL
    left::FormulaPL
    right::FormulaPL
end

"""
    Or_PL(left::FormulaPL, right::FormulaPL) <: FormulaPL

Representa la disyunción de dos fórmulas (φ ∨ ψ).

# Ejemplos
```julia
Or_PL(p, q)  # p ∨ q
```
"""
struct Or_PL <: FormulaPL
    left::FormulaPL
    right::FormulaPL
end

"""
    Imp_PL(left::FormulaPL, right::FormulaPL) <: FormulaPL

Representa la implicación material (φ → ψ).

# Ejemplos
```julia
Imp_PL(p, q)  # p → q
```
"""
struct Imp_PL <: FormulaPL
    left::FormulaPL
    right::FormulaPL
end

"""
    Iff_PL(left::FormulaPL, right::FormulaPL) <: FormulaPL

Representa el bicondicional (φ ↔ ψ).

# Ejemplos
```julia
Iff_PL(p, q)  # p ↔ q
```
"""
struct Iff_PL <: FormulaPL
    left::FormulaPL
    right::FormulaPL
end

# ==================== CONSTANTES LÓGICAS ====================

"""
    Top_PL() <: FormulaPL

Representa la tautología (⊤), una fórmula siempre verdadera.
"""
struct Top_PL <: FormulaPL end

"""
    Bottom_PL() <: FormulaPL

Representa la contradicción (⊥), una fórmula siempre falsa.
"""
struct Bottom_PL <: FormulaPL end

# Constantes globales para uso conveniente
"""
Constante global para la tautología. Equivale a `Top_PL()`.
"""
const ⊤ = Top_PL()

"""
Constante global para la contradicción. Equivale a `Bottom_PL()`.
"""
const ⊥ = Bottom_PL()

# ==================== SOBRECARGA DE OPERADORES ====================

"""
Sobrecarga de operadores de Julia para permitir sintaxis natural en la 
construcción de fórmulas proposicionales.

# Operadores disponibles:
- `!f` o `-f`: Negación (¬f)
- `f1 & f2`  : Conjunción (f1 ∧ f2)
- `f1 | f2`  : Disyunción (f1 ∨ f2)
- `f1 > f2`  : Implicación (f1 → f2)
- `f1 ~ f2`  : Bicondicional (f1 ↔ f2)

# Ejemplos
```julia
formula = (p & q) > (!r | q)  # (p ∧ q) → (¬r ∨ q)
```
"""
Base.:!(f::FormulaPL) = Neg_PL(f)                       #       !f ≡ ¬f
Base.:-(f::FormulaPL) = Neg_PL(f)                       #       -f ≡ ¬f
Base.:&(f1::FormulaPL, f2::FormulaPL) = And_PL(f1, f2)  # f1 & f2  ≡ f1 ∧ f2
Base.:|(f1::FormulaPL, f2::FormulaPL) = Or_PL(f1, f2)   # f1 | f2  ≡ f1 ∨ f2
Base.:>(f1::FormulaPL, f2::FormulaPL) = Imp_PL(f1, f2)  # f1 > f2  ≡ f1 → f2
Base.:~(f1::FormulaPL, f2::FormulaPL) = Iff_PL(f1, f2)  # f1 ~ f2  ≡ f1 ↔ f2

# ==================== FUNCIONES AUXILIARES Y CONSTRUCTORES ====================

"""
Implementa un orden para variables proposicionales basado en sus nombres.
Esto permite que las variables se ordenen alfabéticamente en operaciones como
la generación de tablas de verdad.
"""
Base.isless(v1::Var_PL, v2::Var_PL) = isless(v1.name, v2.name)

"""
    ⋀(Γ::Vector{FormulaPL}) -> FormulaPL

Conjunción de todas las fórmulas en el vector Γ.
Equivale a φ₁ ∧ φ₂ ∧ ... ∧ φₙ.

# Ejemplos
```julia
formulas = [p > q, q, r]
conjunction = ⋀(formulas)  # (p → q) ∧ q ∧ r
```

# Notas
- ⋀ se escribe como \bigwedge<TAB> en Julia
- Utiliza `reduce` internamente para construir la conjunción
"""
function ⋀(Γ::Vector{T}) where T <: FormulaPL
    return reduce(&, Γ) 
end

"""
    ⋁(Γ::Vector{FormulaPL}) -> FormulaPL

Disyunción de todas las fórmulas en el vector Γ.
Equivale a φ₁ ∨ φ₂ ∨ ... ∨ φₙ.

# Ejemplos
```julia
formulas = [p > q, q, r]
disjunction = ⋁(formulas)  # (p → q) ∨ q ∨ r
```

# Notas
- ⋁ se escribe como \bigvee<TAB> en Julia
- Utiliza `reduce` internamente para construir la disyunción
"""
function ⋁(Γ::Vector{T}) where T <: FormulaPL
    return reduce(|, Γ) 
end

"""
    vars(names...) -> Vector{Var_PL}

Función auxiliar para crear múltiples variables proposicionales de forma 
conveniente.

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
variables = vars(:x, :y, :z)
```

# Argumentos
- `names...`: Nombres de las variables (pueden ser strings o símbolos)

# Retorna
Vector de variables proposicionales `Var_PL`.
"""
function vars(names...)
    return [Var_PL(string(name)) for name in names]
end

"""
    @formula expr

Macro para crear fórmulas proposicionales usando sintaxis más natural.
Permite escribir fórmulas usando nombres de variables directamente.

# Ejemplos
```julia
# En lugar de: And_PL(Var_PL("p"), Or_PL(Var_PL("q"), Neg_PL(Var_PL("r"))))
formula = @formula p & (q | !r)
```

# Sintaxis soportada
- Variables    : `p`, `q`, `x1`, etc.
- Negación     : `!p` o `-p`
- Conjunción   : `p & q`
- Disyunción   : `p | q`
- Implicación  : `p > q`
- Bicondicional: `p ~ q`

# Notas
La macro convierte automáticamente símbolos a variables proposicionales.
"""
macro formula(expr)
    return parse_formula(expr)
end

"""
    parse_formula(expr) -> Expr

Función auxiliar que convierte expresiones de Julia en constructores de fórmulas 
proposicionales.
Utilizada internamente por la macro `@formula`.

# Argumentos
- `expr`: Expresión de Julia a convertir

# Funcionamiento
- Símbolos se convierten en `Var_PL`
- Expresiones de llamada se procesan según el operador:
  - `!` o `-`: Negación (`Neg_PL`)
  - `&`: Conjunción (`And_PL`)
  - `|`: Disyunción (`Or_PL`)
  - `>`: Implicación (`Imp_PL`)
  - `~`: Bicondicional (`Iff_PL`)

# Notas
Esta función es recursiva y maneja la precedencia de operadores automáticamente.
"""
function parse_formula(expr)
    if isa(expr, Symbol)
        return :(Var_PL($(string(expr))))
    elseif isa(expr, Expr)
        if expr.head == :call
            op = expr.args[1]
            if (op == :! || op == :-) && length(expr.args) == 2
                return :(Neg_PL($(parse_formula(expr.args[2]))))
            elseif op == :& && length(expr.args) == 3
                return :(And_PL($(parse_formula(expr.args[2])), $(parse_formula(expr.args[3]))))
            elseif op == :| && length(expr.args) == 3
                return :(Or_PL($(parse_formula(expr.args[2])), $(parse_formula(expr.args[3]))))
            elseif op == :> && length(expr.args) == 3
                return :(Imp_PL($(parse_formula(expr.args[2])), $(parse_formula(expr.args[3]))))
            elseif op == :~ && length(expr.args) == 3
                return :(Iff_PL($(parse_formula(expr.args[2])), $(parse_formula(expr.args[3]))))
            end
        end
    end
    error("Expresión no reconocida: $expr")
end

end # module Types
