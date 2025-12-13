"""
# Analysis.Properties - Propiedades Semánticas y Relaciones Lógicas

Este submódulo implementa el análisis de propiedades semánticas fundamentales
de la Lógica Proposicional, incluyendo tautologías, satisfacibilidad,
equivalencias y consecuencia lógica.

## Contenido:
- Verificación de propiedades básicas (TAUT, SAT, UNSAT)
- Análisis de consecuencia lógica (múltiples métodos)
- Equivalencia lógica y simplificaciones
- Reducción de fórmulas con constantes

## Componentes principales:
- `TAUT/SAT/UNSAT`: Propiedades fundamentales
- `LC_*`: Consecuencia lógica por diferentes métodos
- `EQUIV`: Equivalencia lógica
- `simplify_constants`: Simplificación de fórmulas

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module Properties

using ..Types
using ..Evaluation
using ..TruthTables
import Base: show

export TAUT, SAT, UNSAT, LC_Def, LC_TAUT, LC_RA, EQUIV, EQUIV_models,
       simplify_constants

# ==================== PROPIEDADES SEMÁNTICAS BÁSICAS ====================

"""
    TAUT(f::FormulaPL) -> Bool

Verifica si una fórmula es una tautología (siempre verdadera).

# Definición matemática
TAUT(f) ⟺ ∀v ∈ {0,1}^n, v(f) = 1

# Algoritmo Básico
Genera todas las valoraciones posibles y verifica que todas satisfagan la fórmula.

# Ejemplos
```julia
p = vars("p")[1]
tautologia = p | !p  # p ∨ ¬p
result = TAUT(tautologia)  # true

contradiccion = p & !p   # p ∧ ¬p
result2 = TAUT(contradiccion)  # false
```

# Complejidad
O(2^n) donde n es el número de variables en la fórmula.

# Aplicaciones
- Verificación de validez lógica
- Análisis de teoremas
- Optimización de circuitos lógicos
"""
function TAUT(f::FormulaPL)
    vars = sort(collect(vars_of(f)))
    return all(val(f) for val in all_valuations_for(vars))
end

"""
    SAT(f::FormulaPL) -> Bool

Verifica si una fórmula es satisfacible (existe al menos una valoración que la 
hace verdadera).

# Definición matemática
SAT(f) ⟺ ∃v ∈ {0,1}^n, v(f) = 1 ⟺ ¬UNSAT(f)

# Algoritmo
Busca una valoración que satisfaga la fórmula usando evaluación exhaustiva.

# Ejemplos
```julia
p, q = vars("p", "q")
satisfacible = p & q  # p ∧ q
result = SAT(satisfacible)  # true

contradiccion = p & !p  # p ∧ ¬p
result2 = SAT(contradiccion)  # false
```

# Complejidad
O(2^n) en el peor caso, pero puede terminar antes si encuentra un modelo.

# Nota
Este es el famoso problema SAT, NP-completo en general.
"""
function SAT(f::FormulaPL)
    vars = sort(collect(vars_of(f)))
    return any(val(f) for val in all_valuations_for(vars))
end

"""
    UNSAT(f::FormulaPL) -> Bool

Verifica si una fórmula es insatisfacible (siempre falsa, contradicción).

# Definición matemática
UNSAT(f) ⟺ ∀v ∈ {0,1}^n, v(f) = 0 ⟺ TAUT(¬f)

# Algoritmo
Equivale a verificar si la negación de la fórmula es una tautología.

# Ejemplos
```julia
p = vars("p")[1]
contradiccion = p & !p  # p ∧ ¬p
result = UNSAT(contradiccion)  # true

tautologia = p | !p  # p ∨ ¬p
result2 = UNSAT(tautologia)  # false
```

# Relaciones
- UNSAT(f) ⟺ TAUT(¬f)
- UNSAT(f) ⟺ ¬SAT(f)
- UNSAT(f) ⟺ |models(f)| = 0
"""
function UNSAT(f::FormulaPL)
    return TAUT(!f)
end

# ==================== CONSECUENCIA LÓGICA ====================

"""
    LC_Def(Γ::Vector{FormulaPL}, φ::FormulaPL) -> Bool

Verifica consecuencia lógica usando la definición semántica directa.

# Definición matemática
Γ ⊨ φ ⟺ models(Γ) ⊆ models(φ)
Equivalentemente: ∀v ∈ models(Γ), v ∈ models(φ)

# Algoritmo
1. Encuentra todos los modelos de Γ
2. Verifica que todos ellos también sean modelos de φ

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
premisas = [p > q, p]  # p → q, p
conclusion = q         # q
result = LC_Def(premisas, conclusion)  # true (Modus Ponens)
```

# Ventajas
- Implementación directa de la definición
- Interpretación semántica clara
- Útil para análisis teórico
"""
function LC_Def(Γ::Vector{FormulaPL}, φ::FormulaPL)
    return all(v(φ) for v in models(Γ))
end

"""
    LC_TAUT(Γ::Vector{FormulaPL}, φ::FormulaPL) -> Bool

Verifica consecuencia lógica por reducción a tautología.

# Definición matemática
Γ ⊨ φ ⟺ ⊨ (⋀Γ → φ)

# Algoritmo
Construye la implicación (⋀Γ → φ) y verifica si es tautología.

# Ejemplos
```julia
p, q = vars("p", "q")
premisas = [p > q, p]  # p → q, p
conclusion = q         # q
result = LC_TAUT(premisas, conclusion)  # true
```

# Ventajas
- Reduce el problema a verificación de tautología
- Método estándar en sistemas de demostración
- Conexión directa con el teorema de deducción
"""
function LC_TAUT(Γ::Vector{FormulaPL}, φ::FormulaPL)
    return TAUT(⋀(Γ) > φ)
end

"""
    LC_RA(Γ::Vector{FormulaPL}, φ::FormulaPL) -> Bool

Verifica consecuencia lógica por reducción al absurdo.

# Definición matemática
Γ ⊨ φ ⟺ Γ ∪ {¬φ} ⊨ ⊥

# Algoritmo
Añade la negación de la conclusión a las premisas y verifica si el conjunto
resultante es insatisfacible.

# Ejemplos
```julia
p, q = vars("p", "q")
premisas = [p > q, p]  # p → q, p
conclusion = q         # q
result = LC_RA(premisas, conclusion)  # true
```

# Ventajas
- Base de la demostración por contradicción
- Eficiente para detectar inconsistencias
- Método usado en resolución automática
"""
function LC_RA(Γ::Vector{FormulaPL}, φ::FormulaPL)
    return UNSAT(⋀([Γ..., !φ]))
end

# ==================== EQUIVALENCIA LÓGICA ====================

"""
    EQUIV(f1::FormulaPL, f2::FormulaPL) -> Bool

Verifica si dos fórmulas son lógicamente equivalentes.

# Definición matemática
f₁ ≡ f₂ ⟺ ⊨ (f₁ ↔ f₂)

# Algoritmo
Construye el bicondicional (f₁ ↔ f₂) y verifica si es tautología.

# Ejemplos
```julia
p, q = vars("p", "q")
f1 = p > q      # p → q
f2 = !p | q     # ¬p ∨ q
result = EQUIV(f1, f2)  # true
```

# Propiedades
- Reflexiva: f ≡ f
- Simétrica: f₁ ≡ f₂ ⟺ f₂ ≡ f₁
- Transitiva: f₁ ≡ f₂ ∧ f₂ ≡ f₃ ⟹ f₁ ≡ f₃
"""
function EQUIV(f1::FormulaPL, f2::FormulaPL)
    return TAUT(f1 ~ f2)
end

"""
    EQUIV_models(f1::FormulaPL, f2::FormulaPL) -> Bool

Verifica equivalencia lógica comparando conjuntos de modelos.

# Definición matemática
f₁ ≡ f₂ ⟺ models(f₁) = models(f₂)

# Algoritmo
Calcula los modelos de ambas fórmulas y compara los conjuntos.

# Ejemplos
```julia
p, q = vars("p", "q")
f1 = p & q      # p ∧ q
f2 = q & p      # q ∧ p (conmutatividad)
result = EQUIV_models(f1, f2)  # true
```

# Ventajas
- Método alternativo para verificar equivalencia
- Útil para análisis comparativo de modelos
- Puede ser más eficiente en casos específicos
"""
function EQUIV_models(f1::FormulaPL, f2::FormulaPL)
    # f₁ ≡ f₂ ⟺ models(f₁) = models(f₂)
    return Set(models(f1)) == Set(models(f2))
end

# ==================== SIMPLIFICACIÓN DE FÓRMULAS ====================

"""
    simplify_constants(f::FormulaPL) -> FormulaPL

Simplifica una fórmula aplicando reglas de reducción con constantes lógicas.

# Reglas aplicadas
Para conjunción (∧):
- x ∧ ⊥ ≡ ⊥
- x ∧ ⊤ ≡ x
- ⊤ ∧ x ≡ x

Para disyunción (∨):
- x ∨ ⊤ ≡ ⊤
- x ∨ ⊥ ≡ x
- ⊥ ∨ x ≡ x

Para implicación (→):
- ⊥ → x ≡ ⊤
- x → ⊤ ≡ ⊤
- ⊤ → x ≡ x
- x → ⊥ ≡ ¬x

Para bicondicional (↔):
- ⊤ ↔ x ≡ x
- x ↔ ⊤ ≡ x
- ⊥ ↔ x ≡ ¬x
- x ↔ ⊥ ≡ ¬x

Para negación (¬):
- ¬⊤ ≡ ⊥
- ¬⊥ ≡ ⊤

# Ejemplos
```julia
p = vars("p")[1]
formula = p & ⊤         # p ∧ ⊤
simplified = simplify_constants(formula)  # p

formula2 = p | ⊥        # p ∨ ⊥
simplified2 = simplify_constants(formula2)  # p
```

# Aplicaciones
- Optimización de fórmulas antes del procesamiento
- Simplificación de resultados de transformaciones
- Mejora de la legibilidad de fórmulas complejas
"""
function simplify_constants(f::FormulaPL)::FormulaPL
    if isa(f, Union{Var_PL, Top_PL, Bottom_PL})
        return f
    elseif isa(f, Neg_PL)
        simplified = simplify_constants(f.operand)
        if isa(simplified, Top_PL)
            return ⊥
        elseif isa(simplified, Bottom_PL)
            return ⊤
        else
            return !(simplified)
        end
    elseif isa(f, And_PL)
        left = simplify_constants(f.left)
        right = simplify_constants(f.right)
        
        # Reglas de simplificación para ∧
        if isa(left, Bottom_PL) || isa(right, Bottom_PL)
            return ⊥  # x ∧ ⊥ ≡ ⊥
        elseif isa(left, Top_PL)
            return right  # ⊤ ∧ x ≡ x
        elseif isa(right, Top_PL)
            return left  # x ∧ ⊤ ≡ x
        else
            return left & right
        end
    elseif isa(f, Or_PL)
        left = simplify_constants(f.left)
        right = simplify_constants(f.right)
        
        # Reglas de simplificación para ∨
        if isa(left, Top_PL) || isa(right, Top_PL)
            return ⊤  # x ∨ ⊤ ≡ ⊤
        elseif isa(left, Bottom_PL)
            return right  # ⊥ ∨ x ≡ x
        elseif isa(right, Bottom_PL)
            return left  # x ∨ ⊥ ≡ x
        else
            return left | right
        end
    elseif isa(f, Imp_PL)
        left = simplify_constants(f.left)
        right = simplify_constants(f.right)
        
        # Reglas de simplificación para →
        if isa(left, Bottom_PL) || isa(right, Top_PL)
            return ⊤  # ⊥ → x ≡ ⊤, x → ⊤ ≡ ⊤
        elseif isa(left, Top_PL)
            return right  # ⊤ → x ≡ x
        elseif isa(right, Bottom_PL)
            return !(left)  # x → ⊥ ≡ ¬x
        else
            return left > right
        end
    elseif isa(f, Iff_PL)
        left = simplify_constants(f.left)
        right = simplify_constants(f.right)
        
        # Reglas de simplificación para ↔
        if isa(left, Top_PL)
            return right  # ⊤ ↔ x ≡ x
        elseif isa(right, Top_PL)
            return left  # x ↔ ⊤ ≡ x
        elseif isa(left, Bottom_PL)
            return !(right)  # ⊥ ↔ x ≡ ¬x
        elseif isa(right, Bottom_PL)
            return !(left)  # x ↔ ⊥ ≡ ¬x
        else
            return left ~ right
        end
    else
        return f
    end
end

end # module Properties
