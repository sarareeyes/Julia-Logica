"""
# Analysis.TruthTables - Tablas de Verdad y Análisis de Modelos

Este submódulo implementa la generación y análisis de tablas de verdad,
así como funciones para trabajar con modelos y contramodelos de fórmulas.

## Contenido:
- Generación sistemática de tablas de verdad
- Búsqueda de modelos y contramodelos
- Funciones de impresión y visualización
- Análisis de propiedades semánticas

## Componentes principales:
- `truth_table`: Generación completa de tablas de verdad
- `models/countermodels`: Búsqueda de valoraciones específicas
- `print_table`: Visualización de resultados
- Generadores optimizados de valoraciones

## Autor: Fernando Sancho Caparrini
## Curso: Lógica Informática 2025-2026
"""
module TruthTables

using ..Types
using ..Evaluation
import Base: show

export truth_table, models, countermodels, print_table, 
       all_valuations_for, valuation_from_binary

# ==================== GENERADORES DE VALORACIONES ====================

"""
    all_valuations_for(vars::Vector{Var_PL}) -> Generator

Genera las 2^n valoraciones posibles para un conjunto de n variables.

# Algoritmo
Mapea cada número i ∈ [0, 2^n-1] a una valoración donde la representación
binaria de i determina los valores de verdad de las variables.

# Orden
Las variables se procesan en el orden dado, y las valoraciones siguen
el orden lexicográfico binario estándar.

# Ejemplos
```julia
p, q = vars("p", "q")
variables = [p, q]
valoraciones = collect(all_valuations_for(variables))
# Resultado: 4 valoraciones en orden 00, 01, 10, 11
```

# Complejidad
O(2^n) en espacio y tiempo, donde n = |vars|.
"""
function all_valuations_for(vars::Vector{Var_PL})
    n = length(vars)
    
    # Mapea cada i ∈ [0, 2^n-1] a una valoración donde la representación 
    # binaria de i se interpreta como la valoración
    return (valuation_from_binary(vars, i) for i in 0:(2^n - 1))
end

"""
    valuation_from_binary(vars::Vector{Var_PL}, binary_num::Int) -> Valuation

Convierte un número entero a una valoración interpretando su representación binaria.

# Algoritmo
- El bit más significativo corresponde a la primera variable
- 1 representa verdadero, 0 representa falso
- Usa operaciones bitwise para eficiencia

# Ejemplos
```julia
p, q = vars("p", "q")
val = valuation_from_binary([p, q], 3)  # 3 = 11₂
# Resultado: {p => true, q => true}
```

# Parámetros
- `vars`: Vector ordenado de variables
- `binary_num`: Número entero a convertir (debe ser < 2^|vars|)
"""
function valuation_from_binary(vars::Vector{Var_PL}, binary_num::Int)
    n = length(vars)
    val = Valuation()
    
    # Extraer bits usando operaciones bitwise (más eficiente que string)
    for (j, var) in enumerate(vars)
        # El bit j-ésimo (contando desde la izquierda) determina el valor de la variable
        bit_position = n - j
        val[var] = (binary_num >> bit_position) & 1 == 1
    end
    
    return val
end

# ==================== TABLAS DE VERDAD ====================

"""
    truth_table(f::FormulaPL) -> Vector{Tuple{Valuation, Bool}}

Genera la tabla de verdad completa de una fórmula proposicional.

# Retorna
Vector de tuplas donde cada tupla contiene:
- Una valoración (asignación a todas las variables de la fórmula)
- El valor de verdad de la fórmula bajo esa valoración

# Orden
Las variables se ordenan alfabéticamente y las valoraciones siguen
el orden lexicográfico binario estándar (000, 001, 010, 011, ...).
El orden de las variables se hereda del orden alfabético de sus nombres.
Hemos sobrecargado isless del tipo Var_PL para que compare por nombre.

# Ejemplos
```julia
p, q = vars("p", "q")
formula = p & q
table = truth_table(formula)
# Resultado: [(v1, false), (v2, false), (v3, false), (v4, true)]
# donde v1 = {p=0, q=0}, v2 = {p=0, q=1}, v3 = {p=1, q=0}, v4 = {p=1, q=1}
```

# Complejidad
O(2^n) donde n es el número de variables (debido a la complejidad del generador)

# Notas
- El orden alfabético de las variables es determinista y reproducible
- Cada valoración se evalúa exactamente una vez
- El resultado preserva el orden de generación
"""
function truth_table(f::FormulaPL)::Vector{Tuple{Valuation, Bool}}
    vars = sort(collect(vars_of(f)))
    return [(v, v(f)) for v in all_valuations_for(vars)]
end

"""
    truth_table(fs::Vector{FormulaPL}) -> Vector{Tuple{Valuation, Vector{Bool}}}

Genera la tabla de verdad completa para un conjunto de fórmulas proposicionales.

# Retorna
Vector de tuplas donde cada tupla contiene:
- Una valoración (asignación a todas las variables que aparecen en cualquiera de las fórmulas)
- Vector de valores de verdad, uno por cada fórmula en el orden dado

# Ejemplos
```julia
p, q, r = vars("p", "q", "r")
formulas = [p & q, p | r, q > r]
table = truth_table(formulas)
# Resultado: [(v1, [false, false, true]), (v2, [false, false, false]), ...]
# donde cada vector tiene 3 booleanos (uno por cada fórmula)
```

# Complejidad
O(2^n * m) , donde n = |vars|, m = |fs|

# Notas
- Si las fórmulas no comparten variables, se consideran todas las variables
- El orden de evaluación respeta el orden del vector de entrada
- Útil para análisis de consecuencia lógica: Γ ⊨ f
"""
function truth_table(fs::Vector{FormulaPL})::Vector{Tuple{Valuation, Vector{Bool}}}
    if isempty(fs)
        return Vector{Tuple{Valuation, Vector{Bool}}}()
    end

    # Obtener las variables que aparecen en las fórmulas
    all_vars = Set{Var_PL}()
    for f in fs
        union!(all_vars, vars_of(f))
    end
    vars = sort(collect(all_vars))
    
    # Evaluar las 2^n valoraciones sobre las fórmulas
    return [(v, [v(f) for f in fs]) for v in all_valuations_for(vars)]
end

# ==================== BÚSQUEDA DE MODELOS ====================

"""
    models(f::FormulaPL) -> Vector{Valuation}

Encuentra todos los modelos (valoraciones que satisfacen) de una fórmula.

# Definición matemática
models(f) = {v ∈ {0,1}^n | v(f) = 1}

# Ejemplos
```julia
formula = p | q  # p ∨ q
modelos = models(formula)
# Resultado: 3 valoraciones donde al menos una variable es verdadera
```

# Aplicaciones
- Verificación de satisfacibilidad (SAT): |models(f)| > 0
- Conteo de modelos (#SAT): |models(f)|
- Análisis de validez: comparar con el total de valoraciones
"""
function models(f::FormulaPL)::Vector{Valuation}
    # models(f) = {v ∈ {0,1}^n | v(f) = 1}
    vars = sort(collect(vars_of(f)))
    return [val for val in all_valuations_for(vars) if val(f)]
end

"""
    models(Γ::Vector{FormulaPL}) -> Vector{Valuation}

Encuentra todos los modelos de un conjunto de fórmulas (satisfacen todas las 
fórmulas simultáneamente).

# Definición matemática
models(Γ) = models(⋀ Γ) = {v | ∀ φ ∈ Γ, v(φ) = 1}

# Ejemplos
```julia
conjunto = [p > q, q > r]  # p → q, q → r
modelos = models(conjunto)
# Valoraciones que satisfacen ambas implicaciones
```

# Aplicaciones
- Verificación de consecuencia lógica
- Análisis de consistencia de conjuntos de fórmulas
- Resolución de sistemas de restricciones lógicas
"""
function models(Γ::Vector{FormulaPL})::Vector{Valuation}
    # models(Γ) = models(⋀ Γ) = {v | ∀ φ ∈ Γ, v(φ) = 1}
    return models(⋀(Γ))
end

"""
    countermodels(f::FormulaPL) -> Vector{Valuation}

Encuentra todos los contramodelos (valoraciones que no verifican) de una fórmula.

# Definición matemática
countermodels(f) = {v ∈ {0,1}^n | v(f) = 0} = models(¬f)

# Ejemplos
```julia
formula = p & q  # p ∧ q
contramodelos = countermodels(formula)
# Resultado: 3 valoraciones donde al menos una variable es falsa
```

# Aplicaciones
- Búsqueda de contraejemplos
- Análisis de robustez de fórmulas
- Verificación de no-validez
"""
function countermodels(f::FormulaPL)::Vector{Valuation}
    # countermodels(f) = {v ∈ {0,1}^n | v(f) = 0}
    vars = sort(collect(vars_of(f)))
    return [val for val in all_valuations_for(vars) if !val(f)]
end

# ==================== VISUALIZACIÓN DE TABLAS ====================

"""
    print_table(table::Vector{Tuple{Valuation, Bool}})

Imprime una tabla de verdad en formato tabular legible.

# Formato
- Encabezado: nombres de variables + "F" para la fórmula
- Filas: valores 1/0 para cada variable + resultado de la fórmula
- Separador: línea de guiones

# Ejemplo de salida
```
 p	q	F
---------
 0	0	0
 0	1	1
 1	0	1
 1	1	1
```

# Características
- Variables ordenadas alfabéticamente
- Uso de 1/0 en lugar de true/false para claridad
- Alineación automática de columnas
"""
function print_table(table::Vector{Tuple{Valuation, Bool}};tabs="")
    if isempty(table)
        println("Tabla vacía")
        return
    end
    
    # Obtener las variables de la primera valoración
    row1 = table[1] # Obtener la primera valoración y su evaluación
    (val, ev) = row1
    vars = sort(collect(keys(val))) 
    n = length(vars)
    
    # Encabezado
    header = " " * join(vars, "   ") * "   " * "F"
    lenh = length(header) + 1
    println(tabs, header)
    println(tabs, "-" ^ lenh)

    # Generar todas las combinaciones posibles
    for (val, ev) in table        
        # Imprimir fila
        # Convertir valores a 1/0
        row_values = [val[var] ? "1" : "0" for var in vars]  
        row =  tabs * " " * join(row_values, "   ") * "   " * (ev ? "1" : "0")
        println(row)
    end
end

"""
    print_table(table::Vector{Tuple{Valuation, Vector{Bool}}})

Imprime una tabla de verdad para múltiples fórmulas en formato tabular legible.

# Formato
- Encabezado: nombres de variables + "F1", "F2", ..., "Fn" para cada fórmula
- Filas: valores 1/0 para cada variable + resultados de cada fórmula
- Separador: línea de guiones

# Ejemplo de salida
```
 p   q  |  F1  F2  F3
---------------------
 0   0  |  0   0   1
 0   1  |  0   0   0
 1   0  |  0   1   1
 1   1  |  1   1   1
```

# Características
- Variables ordenadas alfabéticamente
- Fórmulas numeradas en orden de aparición
- Uso de 1/0 en lugar de true/false para claridad
- Alineación automática de columnas
"""
function print_table(table::Vector{Tuple{Valuation, Vector{Bool}}};tabs="")
    if isempty(table)
        println("Tabla vacía")
        return
    end
    
    # Obtener las variables y número de fórmulas de la primera fila
    row1 = table[1]
    (val, evals) = row1
    vars = sort(collect(keys(val))) 
    num_formulas = length(evals)
    
    # Construir encabezado
    var_header = join(vars, "   ")
    formula_headers = ["F$i" for i in 1:num_formulas]
    formula_header = join(formula_headers, "  ")
    header = " " * var_header * "  |  " * formula_header
    lenh = length(header) + 1
    
    println(tabs, header)
    println(tabs, "-" ^ lenh)

    # Imprimir filas
    for (val, evals) in table        
        # Convertir valores de variables a 1/0
        var_values = [val[var] ? "1" : "0" for var in vars]
        var_row = join(var_values, "   ")
        
        # Convertir evaluaciones de fórmulas a 1/0
        formula_values = [ev ? "1" : "0" for ev in evals]
        formula_row = join(formula_values, "   ")
        
        row = tabs * " " * var_row * "  |  " * formula_row
        println(row)
    end
end

"""
    print_table(table::Vector{Valuation})

Imprime una colección de valoraciones en formato tabular.

# Formato
Similar a print_table para tablas completas, pero sin columna de resultado.

# Ejemplo de salida
```
 p	q
-------
 0	1
 1	0
 1	1
```

# Usos típicos
- Mostrar modelos/contramodelos de una fórmula
- Presentar soluciones de sistemas lógicos
"""
function print_table(table::Vector{Valuation}; tabs="")
    if isempty(table)
        println("No hay valoraciones")
        return
    end
    
    # Obtener las variables de la primera valoración
    val = table[1] # Obtener la primera valoración
    vars = sort(collect(keys(val))) 
    n = length(vars)
    
    # Encabezado
    header = tabs * " " * join(vars, "   ")
    lenh = length(header) + 1
    println(tabs, header)
    println(tabs, "-" ^ lenh)

    # Generar todas las filas
    for val in table        
        # Imprimir fila
        # Convertir valores a 1/0
        row_values = [val[var] ? "1" : "0" for var in vars] 
        row = tabs * " " * join(row_values, "   ")
        println(row)
    end
end

end # module TruthTables
