"""
# Core.Display - Sistema de Visualización de Fórmulas

Este submódulo implementa las funciones de visualización para las fórmulas 
proposicionales, incluyendo manejo inteligente de precedencia de operadores y 
optimización de paréntesis.

## Contenido:
- Funciones `show` personalizadas para todos los tipos de fórmulas
- Manejo automático de precedencia de operadores
- Optimización de paréntesis redundantes
- Soporte para operadores consecutivos del mismo tipo

## Precedencia de operadores (de mayor a menor):
1. Variables, constantes, negación
2. Conjunción (∧)
3. Disyunción (∨)
4. Implicación (→)
5. Bicondicional (↔)

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module Display

using ..Types
import Base: show

export formation_tree, subformulas

# ==================== FUNCIONES DE VISUALIZACIÓN ====================

"""
Implementaciones personalizadas de `show` para visualizar fórmulas de manera 
legible. Estas funciones manejan la precedencia de operadores y la inserción 
apropiada de paréntesis.
"""

"""
Muestra una variable proposicional usando su nombre.
"""
function Base.show(io::IO, f::Var_PL)
    print(io, f.name)
end

"""
Muestra una negación, añadiendo paréntesis solo cuando es necesario.
La negación tiene alta precedencia, por lo que raramente requiere paréntesis.
"""
function Base.show(io::IO, f::Neg_PL)
    # La negación necesita paréntesis si el operando no es una variable, constante u otra negación
    if isa(f.operand, Union{Var_PL, Top_PL, Bottom_PL, Neg_PL})
        print(io, "¬", f.operand)
    else
        print(io, "¬(", f.operand, ")")
    end
end

"""
    collect_consecutive_operands(f::FormulaPL, op_type::Type, operands::Vector{FormulaPL})

Función auxiliar para recopilar operandos consecutivos del mismo tipo de operador.
Útil para mostrar fórmulas como `p ∧ q ∧ r` en lugar de `((p ∧ q) ∧ r)`.

# Argumentos
- `f`: Fórmula a procesar
- `op_type`: Tipo de operador a buscar (And_PL, Or_PL, etc.)
- `operands`: Vector donde se acumulan los operandos encontrados

# Funcionamiento
Utiliza reflexión (hasfield) para determinar automáticamente si un tipo tiene
campos `left` y `right`, permitiendo un código más genérico.

# Ejemplos
```julia
# Para la fórmula ((p ∧ q) ∧ r), recoge [p, q, r]
operands = collect_consecutive_operands(formula, And_PL)
```
"""
function collect_consecutive_operands(f::FormulaPL, op_type::Type, operands::Vector{FormulaPL} = FormulaPL[])
    if isa(f, op_type) && hasfield(op_type, :left) && hasfield(op_type, :right)
        # Recursión automática para operadores binarios del mismo tipo
        collect_consecutive_operands(f.left, op_type, operands)
        collect_consecutive_operands(f.right, op_type, operands)
    else
        # Operando terminal
        push!(operands, f)
    end
    return operands
end

"""
    needs_parentheses_simple(child::FormulaPL, parent_op::Type) -> Bool

Determina si una subfórmula necesita paréntesis basándose en la precedencia de 
operadores.

# Precedencia (de mayor a menor):
1. Variables, constantes, negación
2. Conjunción (∧)
3. Disyunción (∨)
4. Implicación (→)
5. Bicondicional (↔)

# Reglas implementadas:
- Variables y constantes nunca necesitan paréntesis
- Operadores de menor precedencia necesitan paréntesis dentro de mayor precedencia
- Asociatividad: la implicación es asociativa por la derecha

# Ejemplos
```julia
# p ∨ q dentro de conjunción: (p ∨ q) ∧ r
needs_parentheses_simple(Or_PL(...), And_PL)  # true

# p ∧ q dentro de disyunción: (p ∧ q) ∨ r  
needs_parentheses_simple(And_PL(...), Or_PL)  # true
```
"""
function needs_parentheses_simple(child::FormulaPL, parent_op::Type)
    # Variables, constantes y negaciones nunca necesitan paréntesis
    if isa(child, Union{Var_PL, Top_PL, Bottom_PL, Neg_PL})
        return false
    end
    
    # Para conjunciones como padre
    if parent_op == And_PL
        # Solo las disyunciones, implicaciones y bicondicionales necesitan paréntesis
        if isa(child, Union{Or_PL, Imp_PL, Iff_PL})
            return true
        end
        # Conjunciones consecutivas no necesitan paréntesis
        return false
    end
    
    # Para disyunciones como padre
    if parent_op == Or_PL
        # Solo las implicaciones y bicondicionales necesitan paréntesis
        if isa(child, Union{Imp_PL, Iff_PL})
            return true
        end
        # Conjunciones dentro de disyunciones necesitan paréntesis
        if isa(child, And_PL)
            return true
        end
        # Disyunciones consecutivas no necesitan paréntesis
        return false
    end
    
    # Para implicaciones como padre
    if parent_op == Imp_PL
        # Todas las operaciones binarias necesitan paréntesis EXCEPTO variables y negaciones
        if isa(child, Union{And_PL, Or_PL, Imp_PL, Iff_PL})
            return true
        end
        return false
    end
    
    # Para bicondicionales como padre
    if parent_op == Iff_PL
        # Todas las operaciones binarias necesitan paréntesis EXCEPTO variables y negaciones
        if isa(child, Union{And_PL, Or_PL, Imp_PL, Iff_PL})
            return true
        end
        return false
    end
    
    return false
end

"""
    show_with_parentheses_simple(io::IO, f::FormulaPL, parent_op::Type)

Función auxiliar que muestra una fórmula añadiendo paréntesis si es necesario
según las reglas de precedencia.

# Argumentos
- `io`: Stream de salida
- `f`: Fórmula a mostrar
- `parent_op`: Tipo del operador padre (para determinar precedencia)
"""
function show_with_parentheses_simple(io::IO, f::FormulaPL, parent_op::Type)
    if needs_parentheses_simple(f, parent_op)
        print(io, "(", f, ")")
    else
        print(io, f)
    end
end

"""
Muestra una conjunción (∧), optimizando la visualización de múltiples operandos.
Para fórmulas como ((p ∧ q) ∧ r), muestra p ∧ q ∧ r sin paréntesis redundantes.
"""
function Base.show(io::IO, f::And_PL)
    operands = collect_consecutive_operands(f, And_PL)
    if length(operands) > 2
        # Múltiples operandos: mostrar sin paréntesis externos
        for (i, operand) in enumerate(operands)
            if i > 1
                print(io, " ∧ ")
            end
            show_with_parentheses_simple(io, operand, And_PL)
        end
    else
        # Solo dos operandos
        show_with_parentheses_simple(io, f.left, And_PL)
        print(io, " ∧ ")
        show_with_parentheses_simple(io, f.right, And_PL)
    end
end

"""
Muestra una disyunción (∨), optimizando la visualización de múltiples operandos.
Para fórmulas como ((p ∨ q) ∨ r), muestra p ∨ q ∨ r sin paréntesis redundantes.
"""
function Base.show(io::IO, f::Or_PL)
    operands = collect_consecutive_operands(f, Or_PL)
    if length(operands) > 2
        # Múltiples operandos: mostrar sin paréntesis externos
        for (i, operand) in enumerate(operands)
            if i > 1
                print(io, " ∨ ")
            end
            show_with_parentheses_simple(io, operand, Or_PL)
        end
    else
        # Solo dos operandos
        show_with_parentheses_simple(io, f.left, Or_PL)
        print(io, " ∨ ")
        show_with_parentheses_simple(io, f.right, Or_PL)
    end
end

"""
Muestra una implicación (→), manejando la asociatividad por la derecha.
La implicación es asociativa por la derecha: p → q → r se lee como p → (q → r).
Por tanto, (p → q) → r necesita paréntesis explícitos.
"""
function Base.show(io::IO, f::Imp_PL)
    # Verificar asociatividad: implicación izquierda necesita paréntesis
    if isa(f.left, Imp_PL)
        print(io, "(", f.left, ")")
    else
        show_with_parentheses_simple(io, f.left, Imp_PL)
    end
    print(io, " → ")
    show_with_parentheses_simple(io, f.right, Imp_PL)
end

"""
Muestra un bicondicional (↔), añadiendo paréntesis según precedencia.
El bicondicional tiene la menor precedencia de todos los operadores binarios.
"""
function Base.show(io::IO, f::Iff_PL)
    show_with_parentheses_simple(io, f.left, Iff_PL)
    print(io, " ←→ ")
    show_with_parentheses_simple(io, f.right, Iff_PL)
end

"""
Muestra la constante tautología usando el símbolo ⊤.
"""
function Base.show(io::IO, f::Top_PL)
    print(io, "⊤")
end

"""
Muestra la constante contradicción usando el símbolo ⊥.
"""
function Base.show(io::IO, f::Bottom_PL)
    print(io, "⊥")
end

# ==================== ÁRBOL DE FORMACIÓN ====================

"""
    formation_tree(f::FormulaPL, prefix::String, is_last::Bool) -> String

Genera una representación visual del árbol de formación de una fórmula.
Muestra la estructura jerárquica de la fórmula con formato de árbol ASCII.

# Ejemplos de salida
```
Para p & q:
∧
├── p
└── q

Para (p & q) | r:
∨
├── ∧
│   ├── p
│   └── q
└── r
```

# Argumentos
- `f`: Fórmula a visualizar
- `prefix`: Prefijo para la indentación (uso interno)
- `is_last`: Si es el último hijo en el nivel actual (uso interno)

# Funcionamiento
- Operadores aparecen como nodos internos
- Variables y constantes aparecen como hojas
- Usa caracteres Unicode para dibujar las conexiones del árbol
"""
function formation_tree(f::FormulaPL, prefix::String = "", is_last::Bool = true)
    if isa(f, Var_PL)
        return f.name
    elseif isa(f, Top_PL)
        return "⊤"
    elseif isa(f, Bottom_PL)
        return "⊥"
    elseif isa(f, Neg_PL)
        # Para negaciones simples, mostrar en una línea
        if isa(f.operand, Union{Var_PL, Top_PL, Bottom_PL})
            return "¬ $(f.operand)"
        else
            # Para negaciones complejas, crear subárbol
            operand_tree = formation_tree(f.operand, prefix * "    ", true)
            return "¬\n$(prefix)└── $operand_tree"
        end
    else
        # Para operadores binarios
        operator = if isa(f, And_PL)
            "∧"
        elseif isa(f, Or_PL)
            "∨"
        elseif isa(f, Imp_PL)
            "→"
        elseif isa(f, Iff_PL)
            "←→"
        end
        
        # Construir prefijos para los hijos (manejo de indentación)
        left_prefix = prefix * "│   "    # Continúa la línea vertical
        right_prefix = prefix * "    "   # Espacio en blanco (último hijo)
        
        # Construir árboles para los operandos recursivamente
        left_tree = formation_tree(f.left, left_prefix, false)
        right_tree = formation_tree(f.right, right_prefix, true)
        
        # Formatear la salida con caracteres de conexión
        left_part = "├── $left_tree"    # Rama izquierda (no es la última)
        right_part = "└── $right_tree"  # Rama derecha (es la última)
        
        return "$operator\n$prefix$left_part\n$prefix$right_part"
    end
end

"""
    formation_tree(f::FormulaPL)

Versión de conveniencia que imprime directamente el árbol de formación.
Llama a la versión completa con parámetros por defecto y muestra el resultado.

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
formation_tree((p & q) > r)
```
"""
function formation_tree(f::FormulaPL)
    println(formation_tree(f, "", true))
end

"""
    subformulas(f::FormulaPL) -> Set{FormulaPL}

Obtiene todas las subfórmulas de una fórmula dada.

# Definición
Una subfórmula de φ es cualquier fórmula que aparece como componente de φ,
incluyendo la propia φ.

# Ejemplos
```julia
p, q = vars("p", "q")
formula = p & q
subs = subformulas(formula)  # {p, q, p ∧ q}
```

# Funcionamiento
- Variables y constantes son subfórmulas de sí mismas
- Para operadores unarios: subfórmulas del operando + la fórmula completa
- Para operadores binarios: subfórmulas de ambos operandos + la fórmula completa

# Nota
El resultado incluye siempre la fórmula original como subfórmula de sí misma.
"""
function subformulas(f::FormulaPL)
    if isa(f, Union{Var_PL, Top_PL, Bottom_PL})
        return Set([f])
    elseif isa(f, Neg_PL)
        return union(subformulas(f.operand), Set([f]))
    elseif isa(f, Union{And_PL, Or_PL, Imp_PL, Iff_PL})
        return union(subformulas(f.left), subformulas(f.right), Set([f]))
    else
        return Set{FormulaPL}()
    end
end 

end # module Display
