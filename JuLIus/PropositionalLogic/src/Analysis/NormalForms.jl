"""
# Analysis.NormalForms - Transformaciones a Formas Normales

Este submódulo implementa las transformaciones de fórmulas proposicionales a
formas normales estándar (CNF y DNF), así como estructuras auxiliares para
representar literales, cláusulas y cubos.

## Contenido:
- Transformaciones CNF/DNF completas
- Estructuras para literales, cláusulas y cubos
- Eliminación de implicaciones y normalización de negaciones
- Distribución y simplificación de operadores
- Funciones de extracción y reconstrucción

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module NormalForms

using ..Types
using ..Evaluation
import Base: show, ==, hash

export Literal, Clause, Cube,
       to_CNF, to_DNF, remove_imp, move_negation_in,
       dist_and_or, dist_or_and, demorgan,
       build_CNF_from_clauses, build_DNF_from_cubes,
       extract_clauses_from_CNF, extract_cubes_from_DNF,
       formula_from_literal, complement, are_complementary,
       is_tautological, is_contradictory, has_complementary_literals

# ==================== ESTRUCTURAS PARA FORMAS NORMALES ====================

"""
    Literal

Estructura para representar literales (variables o su negación).

# Campos
- `variable::Var_PL`: La variable proposicional
- `positive::Bool`: `true` para literal positivo, `false` para negativo

# Ejemplos
```julia
p = Var_PL("p")
lit_pos = Literal(p, true)   # p
lit_neg = Literal(p, false)  # ¬p
```
"""
struct Literal
    variable::Var_PL
    positive::Bool
end

function Base.show(io::IO, L::Literal)
    if L.positive
        print(io, L.variable)
    else
        print(io, "¬$(L.variable)")
    end
end

"""
    Clause

Estructura para representar cláusulas (disyunción de literales).

# Campos
- `literals::Set{Literal}`: Conjunto de literales en la cláusula

# Interpretación
Una cláusula representa una disyunción: L₁ ∨ L₂ ∨ ... ∨ Lₙ

# Casos especiales
- Cláusula vacía: ☐ (contradicción)
- Cláusula unitaria: un solo literal
"""
struct Clause
    literals::Set{Literal}
end

function Base.show(io::IO, C::Clause)
    if isempty(C.literals)
        print(io, "☐")  # Cláusula vacía (contradicción)
    elseif length(C.literals) == 1
        print(io, first(C.literals))
    else
        literals_vec = sort(collect(C.literals), by=L -> (L.variable.name, !L.positive))
        print(io, "(", join(literals_vec, " ∨ "), ")")
    end
end

"""
    Cube

Estructura para representar cubos (conjunción de literales).

# Campos
- `literals::Set{Literal}`: Conjunto de literales en el cubo

# Interpretación
Un cubo representa una conjunción: L₁ ∧ L₂ ∧ ... ∧ Lₙ

# Casos especiales
- Cubo vacío: ◯ (tautología)
- Cubo unitario: un solo literal
"""
struct Cube
    literals::Set{Literal}
end

function Base.show(io::IO, C::Cube)
    if isempty(C.literals)
        print(io, "◯")  # Cubo vacío (tautología)
    elseif length(C.literals) == 1
        print(io, first(C.literals))
    else
        literals_vec = sort(collect(C.literals), by=L -> (L.variable.name, !L.positive))
        print(io, "(", join(literals_vec, " ∧ "), ")")
    end
end

# Implementar igualdad y hash para Clause y Cube
function Base.:(==)(c1::Clause, c2::Clause)
    return c1.literals == c2.literals
end

function Base.hash(c::Clause, h::UInt)
    return hash(c.literals, h)
end

function Base.:(==)(c1::Cube, c2::Cube)
    return c1.literals == c2.literals
end

function Base.hash(c::Cube, h::UInt)
    return hash(c.literals, h)
end

# ==================== FUNCIONES AUXILIARES PARA LITERALES ====================

"""
    Literal(f::FormulaPL) -> Literal

Constructor para crear un literal desde una fórmula unitaria.

# Ejemplos
```julia
p = Var_PL("p")
lit1 = Literal(p)      # Literal(p, true)
lit2 = Literal(!p)     # Literal(p, false)
```
"""
function Literal(f::FormulaPL)
    if isa(f, Var_PL)
        return Literal(f, true)
    elseif isa(f, Neg_PL) && isa(f.operand, Var_PL)
        return Literal(f.operand, false)
    else
        error("La fórmula $f no es un literal")
    end
end

"""
    formula_from_literal(L::Literal) -> FormulaPL

Convierte un literal de vuelta a una fórmula.

# Ejemplos
```julia
p = Var_PL("p")
lit = Literal(p, false)
formula = formula_from_literal(lit)  # ¬p (como fórmula)
```
"""
function formula_from_literal(L::Literal)
    return L.positive ? L.variable : !(L.variable)
end

"""
    complement(L::Literal) -> Literal

Crea el complementario de un literal.

# Ejemplos
```julia
p = Var_PL("p")
lit = Literal(p, true)
comp = complement(lit)  # Literal(p, false)
```
"""
function complement(L::Literal)::Literal
    return Literal(L.variable, !L.positive)
end

"""
    are_complementary(L1::Literal, L2::Literal) -> Bool

Verifica si dos literales son complementarios.

# Definición
Dos literales son complementarios si se refieren a la misma variable
pero con polaridades opuestas.

# Ejemplos
```julia
p = Var_PL("p")
lit1 = Literal(p, true)
lit2 = Literal(p, false)
result = are_complementary(lit1, lit2)  # true
```
"""
function are_complementary(L1::Literal, L2::Literal)
    return L1.variable == L2.variable && L1.positive != L2.positive
end

"""
    has_complementary_literals(literals::Set{Literal}) -> Bool

Verifica si hay literales complementarios en un conjunto.

# Utilidad
- En cláusulas: hace la cláusula tautológica (siempre verdadera)
- En cubos: hace el cubo contradictorio (siempre falso)

# Ejemplos
```julia
p, q = vars("p", "q")
lit1 = Literal(p, true)
lit2 = Literal(p, false)
lit3 = Literal(q, true)
lits = Set([lit1, lit2, lit3])
result = has_complementary_literals(lits)  # true
```
"""
function has_complementary_literals(literals::Set{Literal})
    variables_seen = Set{Var_PL}()
    for L in literals
        if L.variable in variables_seen
            # Verificar si existe el complementario
            for other_L in literals
                if are_complementary(L, other_L)
                    return true
                end
            end
        else
            push!(variables_seen, L.variable)
        end
    end
    return false
end

"""
    is_tautological(C::Clause) -> Bool

Verifica si una cláusula es tautológica.

# Definición
Una cláusula es tautológica si contiene literales complementarios,
porque entonces es siempre verdadera: (p ∨ ¬p ∨ ...) ≡ ⊤
"""
function is_tautological(C::Clause)
    return has_complementary_literals(C.literals)
end

"""
    is_contradictory(C::Cube) -> Bool

Verifica si un cubo es contradictorio.

# Definición
Un cubo es contradictorio si contiene literales complementarios,
porque entonces es siempre falso: (p ∧ ¬p ∧ ...) ≡ ⊥
"""
function is_contradictory(C::Cube)
    return has_complementary_literals(C.literals)
end

# ==================== TRANSFORMACIONES BÁSICAS ====================

"""
    remove_imp(f::FormulaPL) -> FormulaPL

Elimina implicaciones y bicondicionales usando equivalencias lógicas.

# Transformaciones aplicadas
- p → q ≡ ¬p ∨ q
- p ↔ q ≡ (p → q) ∧ (q → p) ≡ (¬p ∨ q) ∧ (¬q ∨ p)

# Ejemplos
```julia
p, q = vars("p", "q")
formula = p > q               # p → q
result = remove_imp(formula)  # ¬p ∨ q
```

# Proceso
1. Recursión en subfórmulas
2. Transformación de implicaciones y bicondicionales
3. Preservación de otros operadores
"""
function remove_imp(f::FormulaPL)
    if isa(f, Union{Var_PL, Top_PL, Bottom_PL})
        return f
    elseif isa(f, Neg_PL)
        return !(remove_imp(f.operand))
    elseif isa(f, And_PL)
        return (remove_imp(f.left) & remove_imp(f.right))
    elseif isa(f, Or_PL)
        return (remove_imp(f.left) | remove_imp(f.right))
    elseif isa(f, Imp_PL) # p → q ≡ ¬p ∨ q
        return (!(remove_imp(f.left)) | remove_imp(f.right))
    elseif isa(f, Iff_PL) # p ↔ q ≡ (p → q) ∧ (q → p) ≡ (¬p ∨ q) ∧ (¬q ∨ p)
        left_imp = (!(remove_imp(f.left)) | remove_imp(f.right))
        right_imp = (!(remove_imp(f.right)) | remove_imp(f.left))
        return (left_imp & right_imp)
    else
        return f
    end
end

"""
    move_negation_in(f::FormulaPL) -> FormulaPL

Mueve negaciones exteriores hacia el interior de las fórmulas.

# Transformaciones aplicadas
- ¬¬p ≡ p (eliminación de doble negación)
- ¬(p ∧ q) ≡ ¬p ∨ ¬q (De Morgan)
- ¬(p ∨ q) ≡ ¬p ∧ ¬q (De Morgan)
- ¬⊤ ≡ ⊥, ¬⊥ ≡ ⊤

# Ejemplos
```julia
p, q = vars("p", "q")
formula = !(p & q)                  # ¬(p ∧ q)
result = move_negation_in(formula)  # ¬p ∨ ¬q
```

# Resultado
Fórmula en Forma Normal Negativa (NNF) donde las negaciones
solo aparecen directamente sobre variables.
"""
function move_negation_in(f::FormulaPL)
    if isa(f, Union{Var_PL, Top_PL, Bottom_PL})
        return f
    elseif isa(f, Neg_PL)
        operand = f.operand
        if isa(operand, Union{Var_PL, Top_PL, Bottom_PL})
            if isa(operand, Top_PL)
                return ⊥  # ¬⊤ ≡ ⊥
            elseif isa(operand, Bottom_PL)
                return ⊤  # ¬⊥ ≡ ⊤
            else
                return f  # ¬p se mantiene
            end
        elseif isa(operand, Neg_PL)  # ¬¬p ≡ p
            return move_negation_in(operand.operand)
        elseif isa(operand, And_PL)  # ¬(p ∧ q) ≡ ¬p ∨ ¬q
            return (move_negation_in(!(operand.left)) | move_negation_in(!(operand.right)))
        elseif isa(operand, Or_PL)   # ¬(p ∨ q) ≡ ¬p ∧ ¬q
            return (move_negation_in(!(operand.left)) & move_negation_in(!(operand.right)))
        else
            return !(move_negation_in(operand))
        end
    elseif isa(f, And_PL)
        return (move_negation_in(f.left) & move_negation_in(f.right))
    elseif isa(f, Or_PL)
        return (move_negation_in(f.left) | move_negation_in(f.right))
    elseif isa(f, Union{Imp_PL, Iff_PL})  # Eliminar implicaciones primero
        return move_negation_in(remove_imp(f))  
    else
        return f
    end
end

"""
    demorgan(f::Neg_PL) -> FormulaPL

Aplica las leyes de De Morgan a una negación.

# Leyes aplicadas
- ¬(p ∧ q) ≡ ¬p ∨ ¬q
- ¬(p ∨ q) ≡ ¬p ∧ ¬q

# Ejemplos
```julia
p, q = vars("p", "q")
formula = !(p & q)
result = demorgan(formula)  # ¬p ∨ ¬q
```
"""
function demorgan(f::Neg_PL)
    operand = f.operand
    if isa(operand, And_PL)
        return (!(operand.left) | !(operand.right))
    elseif isa(operand, Or_PL)
        return (!(operand.left) & !(operand.right))
    else
        return f
    end
end

# ==================== DISTRIBUCIÓN PARA CNF Y DNF ====================

"""
    dist_and_or(f::FormulaPL) -> FormulaPL

Distribuye conjunciones sobre disyunciones para obtener CNF.

# Regla de distribución
- (p ∧ q) ∨ r ≡ (p ∨ r) ∧ (q ∨ r)
- p ∨ (q ∧ r) ≡ (p ∨ q) ∧ (p ∨ r)

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
formula = (p & q) | r
result = dist_and_or(formula)  # (p ∨ r) ∧ (q ∨ r)
```
"""
function dist_and_or(f::FormulaPL)
    if isa(f, Union{Var_PL, Top_PL, Bottom_PL}) || isa(f, Neg_PL)
        return f
    elseif isa(f, And_PL)
        left = dist_and_or(f.left)
        right = dist_and_or(f.right)
        return (left & right)
    elseif isa(f, Or_PL)
        left = dist_and_or(f.left)
        right = dist_and_or(f.right)
        
        # Si uno de los operandos es una conjunción, distribuir
        if isa(left, And_PL)       # (p ∧ q) ∨ r ≡ (p ∨ r) ∧ (q ∨ r)
            return (dist_and_or(left.left | right) & dist_and_or(left.right | right))
        elseif isa(right, And_PL)  # p ∨ (q ∧ r) ≡ (p ∨ q) ∧ (p ∨ r)
            return (dist_and_or(left | right.left) & dist_and_or(left | right.right))
        else
            return (left | right)
        end
    elseif isa(f, Imp_PL) || isa(f, Iff_PL) # Eliminar implicaciones y distribuir
        return dist_and_or(remove_imp(f))
    end
end

"""
    dist_or_and(f::FormulaPL) -> FormulaPL

Distribuye disyunciones sobre conjunciones para obtener DNF.

# Regla de distribución
- (p ∨ q) ∧ r ≡ (p ∧ r) ∨ (q ∧ r)
- p ∧ (q ∨ r) ≡ (p ∧ q) ∨ (p ∧ r)

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
formula = (p | q) & r
result = dist_or_and(formula)  # (p ∧ r) ∨ (q ∧ r)
```
"""
function dist_or_and(f::FormulaPL)
    if isa(f, Union{Var_PL, Top_PL, Bottom_PL}) || isa(f, Neg_PL)
        return f
    elseif isa(f, Or_PL)
        left = dist_or_and(f.left)
        right = dist_or_and(f.right)
        return (left | right)
    elseif isa(f, And_PL)
        left = dist_or_and(f.left)
        right = dist_or_and(f.right)
        
        # Si uno de los operandos es una disyunción, distribuir
        if isa(left, Or_PL)       # (p ∨ q) ∧ r ≡ (p ∧ r) ∨ (q ∧ r)
            return (dist_or_and(left.left & right) | dist_or_and(left.right & right))
        elseif isa(right, Or_PL)  # p ∧ (q ∨ r) ≡ (p ∧ q) ∨ (p ∧ r)
            return (dist_or_and(left & right.left) | dist_or_and(left & right.right))
        else
            return (left & right)
        end
    elseif isa(f, Imp_PL) || isa(f, Iff_PL)  # Eliminar implicaciones y distribuir
        return dist_or_and(remove_imp(f))
    end
end

# ==================== EXTRACCIÓN Y CONSTRUCCIÓN ====================

"""
    extract_clauses_from_CNF(f::FormulaPL) -> Set{Clause}

Extrae todas las cláusulas de una fórmula en CNF.

# Proceso
1. Recorre la estructura de conjunciones
2. Convierte cada disyunción de literales en una cláusula
3. Filtra cláusulas tautológicas

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
cnf = (p | q) & (!p | r)
clauses = extract_clauses_from_CNF(cnf)
# Set con dos cláusulas: {p, q} y {¬p, r}
```
"""
function extract_clauses_from_CNF(f::FormulaPL, clauses::Set{Clause}=Set{Clause}())
    if isa(f, And_PL)
        # CNF: procesar conjunciones
        extract_clauses_from_CNF(f.left, clauses)
        extract_clauses_from_CNF(f.right, clauses)
    else
        # Es una cláusula individual
        literals = extract_literals_from_clause(f)
        clause = clause_from(literals)
        if clause !== nothing
            push!(clauses, clause)
        end
    end
    return clauses
end

"""
    extract_cubes_from_DNF(f::FormulaPL) -> Set{Cube}

Extrae todos los cubos de una fórmula en DNF.

# Proceso
1. Recorre la estructura de disyunciones
2. Convierte cada conjunción de literales en un cubo
3. Filtra cubos contradictorios

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
dnf = (p & q) | (!p & r)
cubes = extract_cubes_from_DNF(dnf)
# Set con dos cubos: {p, q} y {¬p, r}
```
"""
function extract_cubes_from_DNF(f::FormulaPL, cubes::Set{Cube}=Set{Cube}())
    if isa(f, Or_PL)
        # DNF: procesar disyunciones
        extract_cubes_from_DNF(f.left, cubes)
        extract_cubes_from_DNF(f.right, cubes)
    else
        # Es un cubo individual
        literals = extract_literals_from_cube(f)
        cube = cube_from(literals)
        if cube !== nothing
            push!(cubes, cube)
        end
    end
    return cubes
end

function extract_literals_from_clause(f::FormulaPL, literals::Set{Literal}=Set{Literal}())
    if isa(f, Var_PL)
        push!(literals, Literal(f, true))
    elseif isa(f, Neg_PL) && isa(f.operand, Var_PL)
        push!(literals, Literal(f.operand, false))
    elseif isa(f, Or_PL)
        extract_literals_from_clause(f.left, literals)
        extract_literals_from_clause(f.right, literals)
    end
    return literals
end

function extract_literals_from_cube(f::FormulaPL, literals::Set{Literal}=Set{Literal}())
    if isa(f, Var_PL)
        push!(literals, Literal(f, true))
    elseif isa(f, Neg_PL) && isa(f.operand, Var_PL)
        push!(literals, Literal(f.operand, false))
    elseif isa(f, And_PL)
        extract_literals_from_cube(f.left, literals)
        extract_literals_from_cube(f.right, literals)
    end
    return literals
end

# Funciones para crear cláusulas y cubos con validación
function clause_from(literals::Set{Literal})
    clause = Clause(literals)
    return is_tautological(clause) ? nothing : clause
end

function cube_from(literals::Set{Literal})
    cube = Cube(literals)
    return is_contradictory(cube) ? nothing : cube
end

# ==================== CONSTRUCCIÓN DE FÓRMULAS ====================

"""
    build_CNF_from_clauses(clauses::Set{Clause}) -> FormulaPL

Construye una fórmula CNF a partir de un conjunto de cláusulas.

# Proceso
1. Convierte cada cláusula a fórmula (disyunción de literales)
2. Combina todas las cláusulas con conjunciones
3. Maneja casos especiales (conjunto vacío, cláusulas vacías)

# Casos especiales
- Conjunto vacío: tautología (⊤)
- Cláusula vacía: contradicción (⊥)
"""
function build_CNF_from_clauses(clauses::Set{Clause})
    if isempty(clauses)
        return ⊤  # Sin cláusulas = tautología
    end
    
    clause_formulas = FormulaPL[]
    
    for clause in clauses
        if isempty(clause.literals)
            return ⊥  # Cláusula vacía = contradicción
        else
            literal_formulas = [formula_from_literal(L) for L in clause.literals]
            if length(literal_formulas) == 1
                push!(clause_formulas, literal_formulas[1])
            else
                push!(clause_formulas, reduce(|, literal_formulas))
            end
        end
    end
    
    return length(clause_formulas) == 1 ? clause_formulas[1] : reduce(&, clause_formulas)
end

"""
    build_DNF_from_cubes(cubes::Set{Cube}) -> FormulaPL

Construye una fórmula DNF a partir de un conjunto de cubos.

# Proceso
1. Convierte cada cubo a fórmula (conjunción de literales)
2. Combina todos los cubos con disyunciones
3. Maneja casos especiales (conjunto vacío, cubos vacíos)

# Casos especiales
- Conjunto vacío: contradicción (⊥)
- Cubo vacío: tautología (⊤)
"""
function build_DNF_from_cubes(cubes::Set{Cube})
    if isempty(cubes)
        return ⊥  # Sin cubos = contradicción
    end
    
    cube_formulas = FormulaPL[]
    
    for cube in cubes
        if isempty(cube.literals)
            return ⊤  # Cubo vacío = tautología
        else
            literal_formulas = [formula_from_literal(L) for L in cube.literals]
            if length(literal_formulas) == 1
                push!(cube_formulas, literal_formulas[1])
            else
                push!(cube_formulas, reduce(&, literal_formulas))
            end
        end
    end
    
    return length(cube_formulas) == 1 ? cube_formulas[1] : reduce(|, cube_formulas)
end

# ==================== FUNCIONES PRINCIPALES DE CONVERSIÓN ====================

"""
    to_CNF(f::FormulaPL) -> FormulaPL

Convierte una fórmula a Forma Normal Conjuntiva (CNF).

# Proceso completo
1. Eliminar implicaciones y bicondicionales
2. Mover negaciones hacia adentro (NNF)
3. Distribuir conjunciones sobre disyunciones
4. Extraer y reconstruir cláusulas (limpieza)

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
formula = (p > q) & (q > r)  # (p → q) ∧ (q → r)
cnf = to_CNF(formula)        # (¬p ∨ q) ∧ (¬q ∨ r)
```

# Resultado
Fórmula equivalente en CNF: conjunción de disyunciones de literales.
"""
function to_CNF(f::FormulaPL)
    # Paso 1: Eliminar implicaciones y bicondicionales
    step1 = remove_imp(f)
    
    # Paso 2: Mover negaciones hacia adentro
    step2 = move_negation_in(step1)
    
    # Paso 3: Distribuir conjunciones sobre disyunciones
    step3 = dist_and_or(step2)
    
    # Paso 4: Extraer cláusulas y reconstruir (opcional para limpieza)
    try
        clauses = extract_clauses_from_CNF(step3)
        return build_CNF_from_clauses(clauses)
    catch
        # Fallback en caso de error
        return step3
    end
end

"""
    to_DNF(f::FormulaPL) -> FormulaPL

Convierte una fórmula a Forma Normal Disyuntiva (DNF).

# Proceso completo
1. Eliminar implicaciones y bicondicionales
2. Mover negaciones hacia adentro (NNF)
3. Distribuir disyunciones sobre conjunciones
4. Extraer y reconstruir cubos (limpieza)

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
formula = (p & q) > r        # (p ∧ q) → r
dnf = to_DNF(formula)        # ¬p ∨ ¬q ∨ r
```

# Resultado
Fórmula equivalente en DNF: disyunción de conjunciones de literales.
"""
function to_DNF(f::FormulaPL)
    # Paso 1: Eliminar implicaciones y bicondicionales
    step1 = remove_imp(f)
    
    # Paso 2: Mover negaciones hacia adentro
    step2 = move_negation_in(step1)
    
    # Paso 3: Distribuir disyunciones sobre conjunciones
    step3 = dist_or_and(step2)
    
    # Paso 4: Extraer cubos y reconstruir (opcional para limpieza)
    try
        cubes = extract_cubes_from_DNF(step3)
        return build_DNF_from_cubes(cubes)
    catch
        # Fallback en caso de error
        return step3
    end
end

end # module NormalForms
