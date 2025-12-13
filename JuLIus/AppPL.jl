include("../JuLIus/PropositionalLogic/src/PropositionalLogic.jl")
using .PropositionalLogic

# ================================================================
# Ejemplo: Rectángulos 
# ================================================================

b,h,b_A,h_A,b_B,h_B,b_C,h_C,b_D,h_D,b_E,h_E,b_F,h_F = vars("b","h","b_A","h_A","b_B","h_B","b_C","h_C","b_D","h_D","b_E","h_E","b_F","h_F")

R = [b_A | h_A, 
    b_B | h_B, 
    b_C | h_C, 
    b_D | h_D, 
    b_E | h_E, 
    b_F | h_F,
    b_A ~ b_C, 

    b_A & b_D > b_F, 
    b_F & b_A > b_D,
    b_F & b_D > b_A,
    
    b_D & b_E > b_B, 
    b_B & b_D > b_E,
    b_B & b_E > b_D,
    
    b_A & b_B > b,
    b & b_A > b_B,
    b & b_B > b_A,
    
    b_F & b_E > b,
    b & b_F > b_E,
    b & b_E > b_F,

    b_A & b_D & b_E > b,
    b & b_A & b_D > b_E,
    b & b_A & b_E > b_D,
    b & b_D & b_E > b_A,

    h_D & h_F > h_E, 
    h_E & h_D > h_F,
    h_E & h_F > h_D,

    h_A & h_C & h_F > h,
    h & h_A & h_C > h_F,
    h & h_A & h_F > h_C,
    h & h_C & h_F > h_A,
    
    h_B & h_D & h_F > h,
    h & h_B & h_D > h_F,
    h & h_B & h_F > h_D,
    h & h_D & h_F > h_B,

    h_B & h_E > h,
    h & h_B > h_E,
    h & h_E > h_B]

LC_Def(R, b | h)
DPLL_LC(R, b | h)

# ================================================================
# 
# ================================================================

#=
En los siguientes problemas trabajaremos con fórmulas parametrizadas, donde el 
número de variables que intervienen puede depender de la instancia del problema 
y, por tanto, no pueden ser declaradas a mano de forma sencilla (también puede 
ocurrir que el número de variables sea muy grande y prefiramos automatizar el 
proceso). Para ello, usaremos bucles y estructuras de datos de Julia 
(normalmente, arrays y diccionarios en sus diversas variedades) para crear las 
variables y las fórmulas que las relacionan.

Se debe tener presente que los problemas pocas veces se describen completamente 
y algunas de sus restricciones se basan en un conocimiento a priori no explícito 
que ha de ser representado también formalmente. A esta información imprescindible 
pero no explícita se le suele llamar "marco" o "contexto" del problema.

Vamos a intentar seguir patrones similares a los que se usan en la teoría para 
definir las fórmulas, de forma que el paso de la definición matemática a la 
implementación sea lo más directo posible.

Los pasos que seguiremos para cada problema serán:
   1. Definir las variables proposicionales que intervienen en el problema, 
      normalmente como una colección (vector, matriz, diccionario, etc.) de 
      variables.
   2. Definir las fórmulas, o conjunto de fórmulas, que representan las 
      restricciones y contexto (marco) del problema, normalmente como una 
      conjunción de varias fórmulas parciales.
   3. Usar DPLL para resolver el problema, normalmente verificando la 
      satisfactibilidad de la conjunción de todas las restricciones.
   4. Interpretar la solución obtenida (si la hay) para el problema concreto.
   5. Visualizar la solución (opcional).
   6. Probar con varias instancias del problema.


Variables y Fórmulas Parametrizadas
-----------------------------------

* Estructura base: Vector	

   Ejemplo 1:
      p = Vector{Var_PL}(undef, N)
      for i in 1:N
         p[i] = Var_PL("p_$i")
      end

   Ejemplo 2:
      p = [Var_PL("p_$i") for i in 1:N]

   Acceso/Muestra: p[1]/ p_1

* Estructura base: Matriz

   Ejemplo 1:
      p = Matrix{Var_PL}(undef, N, M)
      for i in 1:N, j in 1:M
         p[i, j] = Var_PL("p($i,$j)")
      end

   Ejemplo 2:
      p = [Var_PL("p($i,$j)") for i in 1:N, j in 1:M]

   Acceso/Muestra: p[1,1]/ p(1,1)

* Estructura base: Diccionario

   Ejemplo 1:
      p = Dict{Tuple{A,B}, Var_PL}()
      for a in A, b in B
         p[(a,b)] = Var_PL("p($a,$b)")
      end

   Ejemplo 2:
      p = Dict((a, b) => Var_PL("p($a,$b)") for a in A, b in B)

   Acceso/Muestra: p[(a1,b1)]/p(a1,b1)

=#

# ================================================================
## Función "exactamente una"
# ================================================================

#=
Comenzamos definiendo una función que significa "exactamente uno" (∃_{=1} = ∃!) 
y que será de utilidad para los problemas siguientes. Esta función recibe un 
conjunto de variables proposicionales y devuelve la fórmula proposicional que 
se verifica cuando exactamente una, y solo una, de las variables de entrada es 
verdadera:

 ∃_{=1} (v_1,...,v_n) = ( ∃_{>=1} (v_1,...,v_n) )  ∧  ( ∃_{<=1} (v_1,...,v_n) )
 ∃_{=1} (v_1,...,v_n) = (⋁_{i=1..n} v_i) ∧ (⋀_{i=1..n-1} ⋀_{j=i+1..n} ¬(v_i ∧ v_j))

Observa que en el proceso de creación de la fórmula se usan los operadores `⋀` 
y `⋁` para crear las conjunciones y disyunciones de varias fórmulas, y que 
internamente hacemos uso de dos "operadores" intermedios: "al menos una" 
(∃_{>=1}) y "a lo sumo una" (∃_{<=1}).

Por ejemplo: ∃_{=1} (v1,v2,v3) = (v1 ∨ v2 ∨ v3) ∧ ( ¬(v1 ∧ v2) ∧ ¬(v1 ∧ v3) ∧ ¬(v2 ∧ v3) )
=# 

function Ex1(vps::Vector{Var_PL})
    if length(vps) == 0
        error("No se puede crear restricción exactamente_una con lista vacía")
    elseif length(vps) == 1
        return vps[1]
    end
    
    # Al menos una
    al_menos_una = ⋁(vps)
    
    # A lo sumo una: para cada par, ¬(a ∧ b)
    a_lo_sumo_una = ⋀([!(vps[i] & vps[j]) for i in 1:length(vps) for j in (i+1):length(vps)])
    
    return al_menos_una & a_lo_sumo_una
end


# ================================================================
# Problema de las N-reinas 
# ================================================================

#=
Vamos a suponer que tenemos una matriz de variables proposicionales r(i,j) con 
la interpretación:

                r(i,j) = 1 ⟺ hay una reina en la casilla (i,j)

Función que crea la fórmula general que contiene todas las restricciones que 
definen una solución del problema:

   * Una única reina por fila:         
                ⋀_{i=1..n} ∃_{=1}(r_{i,j})_{j=1..n}

   * Una única reina por columna:      
                ⋀_{j=1..n} ∃_{=1}(r_{i,j})_{i=1..n}

   * A lo sumo, una reina por diagonal principal: 
                ⋀_{i=1..n} ∃_{≤ 1} (D^1_{i}), 
      donde D^1_i es el conjunto de casillas de la diagonal principal i-ésima.

   * A lo sumo, una reina por diagonal secundaria: 
                ⋀_{i=1..n} ∃_{≤ 1} (D^2_{i}), 
      donde D^2_i es el conjunto de casillas de la diagonal secundaria i-ésima.
=#



# Función para el problema de las N-reinas
function formula_n_reinas(r::Matrix{Var_PL}, n::Int)        
    # Restricción 1: Exactamente una reina por fila
    Fila(i) = Ex1([r[i, j] for j in 1:n])
    Filas = [Fila(i) for i in 1:n]
    
    # Restricción 2: Exactamente una reina por columna
    Columna(j) = Ex1([r[i, j] for i in 1:n])
    Columnas = [Columna(j) for j in 1:n]
    
    # Restricción 3: A lo sumo una reina por diagonal principal (↘)

    Diag = Dict{Int, FormulaPL}()

    idx = 1
    for k in -(n-2):(n-2)  # Diagonales paralelas a la principal
        D(k) = [ r[i, j] for i in 1:n, j in 1:n if i-j == k ]
        dk = length(D(k))
        if dk > 1 
            Diag[idx] = ⋀([!(D(k)[i] & D(k)[j]) for i in 1:dk for j in (i+1):dk])
            idx = idx + 1
        end
    end
    Diags1 = [F for (key, F) in Diag]
    
    # Restricción 4: A lo sumo una reina por diagonal secundaria (↙)

    Diag = Dict{Int, FormulaPL}()

    idx = 1
    for k in 2:(2*n)   # Diagonales paralelas a la secundaria
        D(k) = [ r[i, j] for i in 1:n, j in 1:n if j == k - i]
        dk = length(D(k))
        if dk > 1 
            Diag[idx] = ⋀([!(D(k)[i] & D(k)[j]) for i in 1:dk for j in (i+1):dk])
            idx = idx + 1
        end
    end
    Diags2 = [F for (key, F) in Diag] 

    return [Filas ; Columnas ; Diags1 ; Diags2]
end

# Función para visualizar la solución de N-reinas
function visual_sol_n_reinas(solution_dict, r, n::Int)
    println("\nRepresentación del tablero $n×$n:")
    # Rellenado del tablero vacío
    tablero = fill("▢", n, n)
    # Colocación de reinas de solución
    for i in 1:n
        for j in 1:n
            if solution_dict[r[i,j]]
                tablero[i, j] = "♕"
            end
        end
    end
    
    # Mostrar el tablero
    for i in 1:n
        println(join(tablero[i, :], " "))
    end
    
    # Contar reinas colocadas
    queen_count = count(==("♕"), tablero)
    println("\nReinas colocadas: $queen_count/$n")
    
    return tablero
end

# Ejemplo de uso:
function test_n_reinas(n::Int)
    println("Probando N-reinas para N=$n")

    # Generar variables r_{ij} - reina en fila i, columna j
    r = Matrix{Var_PL}(undef, n, n)
    for i in 1:n, j in 1:n
        r[i,j] = Var_PL("r($i,$j)")
    end

    # Crear la fórmula 
    formula = formula_n_reinas(r, n);

    # Resolver
    sat, sol = DPLL(formula);
    #sol = TS_solve(formula)
    
    # Representar
    if sat == false
        println("No hay solución para $n reinas.")
    else
        println("Solución encontrada:")
        visual_sol_n_reinas(sol, r, n)
    end
end

# Ejemplo de uso:
test_n_reinas(8);

# ================================================================
# Problema del Sudoku
# ================================================================

#=
El problema del Sudoku se puede resolver de forma similar, pero teniendo en 
cuenta ahora que las variables proposicionales serán de la forma $S(i,j,k)$ con 
la interpretación:

            S(i,j,k) = 1 ⟺ en la casilla (i,j) está el número k

Las restricciones que tenemos que considerar son:

   * Hay exactamente un número en cada casilla:
            ⋀_{i=1..9} ⋀_{j=1..9} ∃_{=1} ({S(i,j,k)}_{k=1..9})

   * Hay exactamente una ocurrencia de cada número por cada fila:
            ⋀_{i=1..9} ⋀_{k=1..9} ∃_{=1} ({S(i,j,k)}_{j=1..9})

   * Hay exactamente una ocurrencia de cada número por cada columna:
            ⋀_{j=1..9} ⋀_{k=1..9} ∃_{=1} ({S(i,j,k)}_{i=1..9})

   * Hay exactamente una ocurrencia de cada número por cada bloque 3×3:
            ⋀_{B ∈ Bloque} ⋀_{(i,j) ∈ B} ∃_{=1} ({S(i,j,k)}_{k=1..9})

   * Además, habrá que añadir las celdas que vienen ya prefijadas/rellenas.
=#

function formula_sudoku(S::Array{Var_PL}, Rellenas::Vector{Tuple{Int, Int, Int}} = [] )    
    # Exactamente un número por celda
    celda(i,j) = Ex1([S[i, j, k] for k in 1:9])
    Celdas = [celda(i, j) for i in 1:9 for j in 1:9]
    
    # Exactamente una ocurrencia de cada número por fila
    Fila(i,k) = Ex1([S[i, j, k] for j in 1:9])
    Filas = [Fila(i, k) for i in 1:9 for k in 1:9]
    
    # Exactamente una ocurrencia de cada número por columna
    Columna(j,k) = Ex1([S[i, j, k] for i in 1:9])
    Columnas = [Columna(j, k) for j in 1:9 for k in 1:9]

    # Exactamente una ocurrencia de cada número por bloque de Sudoku
    Bloque(i, j, k) = Ex1([S[i + bi, j + bj, k] for bi in 0:2 for bj in 0:2])
    Bloques = [Bloque(i, j, k) for i in [1 4 7] for j in [1 4 7] for k in 1:9]

    # Restricciones de celdas ya rellenadas
    Rellenas = [S[i, j, k] for (i, j, k) in Rellenas]

    return [Celdas ; Filas ; Columnas ; Bloques ; Rellenas]
end

# Función para visualizar la solución de N-reinas
function visual_sol_sudoku(solution_dict, S)
    println("\nVisualización de la Solución:")
    tablero = fill(0, 9, 9)
    
    # Procesar cada variable en la solución
    for i in 1:9, j in 1:9, k in 1:9
        var = S[i,j,k]
        if solution_dict[var]
            tablero[i,j] = k
        end
    end

    # Mostrar el tablero
    for i in 1:9
        println(join(tablero[i, :], " "))
    end
    
    return tablero
end

# Ejemplo de uso:
function test_sudoku()
    println("Probando Sudoku")
    
    # Variables S(i,j,k) - número k en posición (i,j)
    S = Array{Var_PL}(undef, 9, 9, 9)
    for i in 1:9, j in 1:9, k in 1:9
        S[i,j,k] = Var_PL("S($i,$j,$k)")
    end

    formula = formula_sudoku(S, [(1, 1, 1), (1, 2, 2), (1, 3, 3), (1, 4, 4), 
                              (1, 5, 5), (1, 6, 6), (1, 7, 7), (1, 8, 8), 
                              (1, 9, 9)]);
    sat, sol = DPLL(formula)
    
    if sat == false
        println("No hay solución para el Sudoku.")
    else
        println("Solución encontrada:")
        visual_sol_sudoku(sol, S)
    end
end

test_sudoku();

# ================================================================
# Coloreado de Mapas
# ================================================================

#=
Un problema similar es el de coloreado de mapas, donde se supone que tenemos un 
conjunto de paises (P, una colección de cadenas, por ejemplo), indicando qué 
pares de países comparten frontera (F) y K colores (que podemos considerarlos 
como números consecutivos). Entonces las restricciones de un coloreado válido 
serían:

   * Todos los países deben estar coloreados con exactamente un único color:
                ⋀_{p ∈ P} ∃_{=1} ({C(p,c)}_{c=1..K})

   * Dos países que compartan frontera deben tener coloreados distintos:
                ⋀_{(p_1,p_2) ∈ F} ⋀_{c=1..K} ¬( C(p_1,c) ∧ C(p_2,c) )
=#

# Función para el problema del coloreado de mapas
function formula_coloreado_mapas(paises::Vector{String}, fronteras::Vector{Tuple{String, String}}, C, num_colores::Int = 4)

    # Restricción 1: Cada país debe tener exactamente un color
    pais_color(pais) = Ex1([C[(pais, color)] for color in 1:num_colores])
    Colores_Paises = [pais_color(pais) for pais in paises]
    
    # Restricción 2: Países que comparten frontera no pueden tener el mismo color
    fronteras_diferentes = [ !(C[(p1, c)] & C[(p2, c)]) for (p1, p2) in fronteras for c in 1:num_colores ]
    Fronteras = fronteras_diferentes

    return [Colores_Paises ; Fronteras]
end

# Función para visualizar la solución del coloreado de mapas
function visual_sol_coloreado_mapas(solution_dict, paises::Vector{String}, C, num_colores::Int = 4)
    println("\nVisualización del Coloreado de Mapas:")
        
    # Mostrar el coloreado
    println("┌─────────────────────────────┬──────────────┐")
    println("│            País             │    Color     │")
    println("├─────────────────────────────┼──────────────┤")
    
    for pais in sort(paises), color_num in 1:num_colores
        var = C[(pais, color_num)]
        if solution_dict[var]
            println("│ $(rpad(pais, 27)) │ $(rpad(color_num, 12)) │")
        end
    end
    
    println("└─────────────────────────────┴──────────────┘")    
end

# Función para probar el coloreado de mapas
function test_coloreado_mapas(paises::Vector{String}, fronteras::Vector{Tuple{String, String}}, num_colores::Int = 4)
    println("Probando coloreado de mapas con $(length(paises)) países y $num_colores colores")
    println("Países: $(join(paises, ", "))")
    println("Fronteras: $(length(fronteras)) conexiones")
    
    # Generar variables C(pais, color) - país tiene color
    C = Dict{Tuple{String, Int}, Var_PL}()
    for pais in paises, color in 1:num_colores
        C[(pais, color)] = Var_PL("C($pais,$color)")
    end

    formula = formula_coloreado_mapas(paises, fronteras, C, num_colores)
    sat, sol = DPLL(formula)
    
    if sat == false
        println("No hay solución para el coloreado con $num_colores colores.")
        return sat, sol
    else
        println("¡Solución encontrada!")
        visual_sol_coloreado_mapas(sol, paises, C, num_colores)
        return sat, sol
    end
end

# Ejemplos de uso del coloreado de mapas

# Ejemplo 1: Mapa simple de 4 países
println("=== EJEMPLO 1: Mapa Simple ===")
paises_simple = ["España", "Francia", "Italia", "Alemania"]
fronteras_simple = [("España", "Francia"), ("Francia", "Italia"), 
                   ("Francia", "Alemania"), ("Italia", "Alemania")]

test_coloreado_mapas(paises_simple, fronteras_simple, 3)

# Ejemplo 2: Mapa más complejo (grafo completo K5 - requiere 5 colores)
println("\n=== EJEMPLO 2: Grafo Completo K5 ===")
paises_k5 = ["A", "B", "C", "D", "E"]
fronteras_k5 = [(paises_k5[i], paises_k5[j]) for i in 1:5 for j in (i+1):5]

test_coloreado_mapas(paises_k5, fronteras_k5,5)

# Ejemplo 3: Algunos países europeos reales
println("\n=== EJEMPLO 3: Europa Occidental ===")
paises_europa = ["España", "Francia", "Alemania", "Italia", "Suiza", "Austria", "Bélgica"]
fronteras_europa = [
    ("España", "Francia"),
    ("Francia", "Alemania"), ("Francia", "Italia"), ("Francia", "Suiza"), ("Francia", "Bélgica"),
    ("Alemania", "Austria"), ("Alemania", "Suiza"), ("Alemania", "Bélgica"),
    ("Italia", "Suiza"), ("Italia", "Austria"),
    ("Suiza", "Austria")
]

test_coloreado_mapas(paises_europa, fronteras_europa, 3)

# ================================================================
# Casas Coloreadas
# ================================================================

"""
    Ejercicio A1: Puzzle Lógico - Casas Coloreadas
    
DESCRIPCIÓN:
Tres casas en fila, cada una con un color, un tipo de vivienda.
Resolver el puzzle con restricciones semánticas.

VARIABLES (diccionario):
- C[(casa, color)] = "la casa tiene ese color"
- H[(casa, hab)] = "la casa tiene ese tipo de vivienda"

RESTRICCIONES:
1. Cada casa tiene exactamente un color
2. Cada color aparece exactamente una vez
3. Restricciones espaciales (vecindad)
4. Restricciones de atributos

OBJETIVO: Determinar la configuración única de las 3 casas
"""

function casas_coloreadas()
    println("\n" * "─"^60)
    println("EJERCICIO A1: Puzzle Lógico - Casas Coloreadas")
    println("─"^60)
    
    casas = 1:3
    colores = ["Rojo", "Verde", "Azul"]
    tipos = ["Piso", "Casa", "Cabaña"]
    
    println("✓ 3 casas en fila (posiciones 1, 2, 3)")
    println("✓ Atributos: Colores = $(join(colores, ", "))")
    println("✓              Tipos = $(join(tipos, ", "))")
    
    # 1. VARIABLES (usando diccionarios)
    C = Dict((c, col) => Var_PL("C($c,$col)") for c in casas, col in colores)
    H = Dict((c, tipo) => Var_PL("H($c,$tipo)") for c in casas, tipo in tipos)
    
    # 2. RESTRICCIONES
    restricciones = FormulaPL[]
    
    # R1: Cada casa tiene exactamente un color
    for c in casas
        push!(restricciones, Ex1([C[(c, col)] for col in colores]))
    end
    println("\n✓ R1: Cada casa tiene un color único")
    
    # R2: Cada color aparece exactamente una vez
    for col in colores
        push!(restricciones, Ex1([C[(c, col)] for c in casas]))
    end
    println("✓ R2: Cada color aparece exactamente una vez")
    
    # R3: Cada casa tiene exactamente un tipo
    for c in casas
        push!(restricciones, Ex1([H[(c, tipo)] for tipo in tipos]))
    end
    println("✓ R3: Cada casa tiene un tipo único")
    
    # R4: Cada tipo aparece exactamente una vez
    for tipo in tipos
        push!(restricciones, Ex1([H[(c, tipo)] for c in casas]))
    end
    println("✓ R4: Cada tipo aparece exactamente una vez")
    
    # R5-R8: Restricciones específicas del puzzle
    # La casa roja está al lado de la casa azul
    # (si la roja está en posición 1, la azul en 2; o roja en 2, azul en 1 ó 3; etc.)
    roja_azul = FormulaPL[]
    for c1 in casas, c2 in casas
        if abs(c1 - c2) == 1  # Son vecinas
            push!(roja_azul, (C[(c1, "Rojo")] & C[(c2, "Azul")]) | (C[(c1, "Azul")] & C[(c2, "Rojo")]))
        end
    end
    push!(restricciones, ⋁(roja_azul))
    println("✓ R5: Rojo y Azul están en casas vecinas")
    
    # El piso es de color verde
    for c in casas
        push!(restricciones, (H[(c, "Piso")] > C[(c, "Verde")]))
    end
    println("✓ R6: El Piso es de color Verde")
    
    # La cabaña es roja
    for c in casas
        push!(restricciones, (H[(c, "Cabaña")] > C[(c, "Rojo")]))
    end
    println("✓ R7: La Cabaña es Roja")
    
    # La casa está en posición 2 (del medio)
    push!(restricciones, H[(2, "Casa")])
    println("✓ R8: La Casa está en el medio (posición 2)")
    
    # 3. RESOLVER
    println("\n⏳ Resolviendo...")
    sat, solucion = DPLL(restricciones)
    
    # 4. MOSTRAR RESULTADO
    println("\n📊 Resultado:")
    if sat
        println("✓ Puzzle RESUELTO\n")
        println("Configuración de las 3 casas:")
        println("┌──────────┬─────────┬──────────┐")
        println("│  Casa    │  Color  │   Tipo   │")
        println("├──────────┼─────────┼──────────┤")
        for c in casas
            color = [col for col in colores if solucion[C[(c, col)]] == 1][1]
            tipo = [t for t in tipos if solucion[H[(c, t)]] == 1][1]
            println("│ Pos. $c   │ $(rpad(color, 7)) │ $(rpad(tipo, 8)) │")
        end
        println("└──────────┴─────────┴──────────┘")
    else
        println("✗ No hay solución para este puzzle")
    end
    
    return sat, solucion
end

# Ejecutar
casas_coloreadas()


# ================================================================
# Acertijo de Einstein
# ================================================================

#=
El famoso **acertijo de Einstein** (también conocido como **Zebra Puzzle**) nos 
dice que hay 5 casas en fila, cada una de ellas con diferentes características, 
pero no nos dicen qué característica corresponde a cada casa:
 - Nacionalidades: Británico, Sueco, Danés, Noruego, Alemán
 - Colores: Rojo, Verde, Amarillo, Azul, Blanco
 - Mascotas: Perro, Pájaro, Gato, Caballo, Pez (Pez Cebra, de ahí el nombre del 
   puzzle)
 - Bebidas: Té, Café, Leche, Cerveza, Agua
 - Cigarrillos: Pall Mall, Dunhill, Blend, Blue Master, Prince

Pero sí nos dan información acerca de posibles relaciones y restricciones 
existente:
 1. El británico vive en la casa roja
 2. El sueco tiene un perro
 3. El danés bebe té
 4. La casa verde está inmediatamente a la izquierda de la casa blanca
 5. El dueño de la casa verde bebe café
 6. La persona que fuma Pall Mall tiene un pájaro
 7. El dueño de la casa amarilla fuma Dunhill
 8. El hombre en la casa del medio bebe leche
 9. El noruego vive en la primera casa
 10. El hombre que fuma Blend vive al lado del que tiene un gato
 11. El hombre que tiene un caballo vive al lado del que fuma Dunhill
 12. El hombre que fuma Blue Master bebe cerveza
 13. El alemán fuma Prince
 14. El noruego vive al lado de la casa azul
 15. El hombre que fuma Blend vive al lado del que bebe agua

 El objetivo es indicar claramente qué características tiene cada casa.
=#

function formula_acertijo_einstein()
    # Definir los conjuntos de características
    nacionalidades = ["Britanico", "Sueco", "Danes", "Noruego", "Aleman"]
    colores = ["Rojo", "Verde", "Amarillo", "Azul", "Blanco"]
    mascotas = ["Perro", "Pajaro", "Gato", "Caballo", "Pez"]
    bebidas = ["Te", "Cafe", "Leche", "Cerveza", "Agua"]
    cigarrillos = ["PallMall", "Dunhill", "Blend", "BlueMaster", "Prince"]
    
    # Variables: X(casa, caracteristica) - la casa tiene esa característica
    N = Dict{Tuple{Int, String}, Var_PL}()  # Nacionalidades
    C = Dict{Tuple{Int, String}, Var_PL}()  # Colores
    M = Dict{Tuple{Int, String}, Var_PL}()  # Mascotas
    B = Dict{Tuple{Int, String}, Var_PL}()  # Bebidas
    F = Dict{Tuple{Int, String}, Var_PL}()  # Cigarrillos (Smoking)
    
    # Generar todas las variables
    for casa in 1:5
        for nac in nacionalidades
            N[(casa, nac)] = Var_PL("N($casa,$nac)")
        end
        for col in colores
            C[(casa, col)] = Var_PL("C($casa,$col)")
        end
        for mas in mascotas
            M[(casa, mas)] = Var_PL("M($casa,$mas)")
        end
        for beb in bebidas
            B[(casa, beb)] = Var_PL("B($casa,$beb)")
        end
        for cig in cigarrillos
            F[(casa, cig)] = Var_PL("F($casa,$cig)")
        end
    end
    
    # RESTRICCIONES BÁSICAS: 
    
    # Cada casa tiene exactamente una nacionalidad, color, mascota, bebida y 
    # cigarrillo
    Basicas = [ [Ex1([N[(casa, nac)] for nac in nacionalidades]) for casa in 1:5] ;
              [Ex1([C[(casa, col)] for col in colores]) for casa in 1:5] ; 
              [Ex1([M[(casa, mas)] for mas in mascotas]) for casa in 1:5] ;
              [Ex1([B[(casa, beb)] for beb in bebidas]) for casa in 1:5] ;
              [Ex1([F[(casa, cig)] for cig in cigarrillos]) for casa in 1:5] ]

    # Cada característica aparece en exactamente una casa
    Caracteristicas = [ [Ex1([N[(casa, nac)] for casa in 1:5]) for nac in nacionalidades] ;
                      [Ex1([C[(casa, col)] for casa in 1:5]) for col in colores] ;
                      [Ex1([M[(casa, mas)] for casa in 1:5]) for mas in mascotas] ;
                      [Ex1([B[(casa, beb)] for casa in 1:5]) for beb in bebidas] ;
                      [Ex1([F[(casa, cig)] for casa in 1:5]) for cig in cigarrillos] ]

    # RESTRICCIONES DEL ACERTIJO
    rest = Vector{Vector{FormulaPL}}(undef, 15)  # Vector para las restricciones 
                                                 # del acertijo
    
    # 1. El británico vive en la casa roja
    rest[1] = [ (N[(casa, "Britanico")] ~ C[(casa, "Rojo")]) for casa in 1:5 ]
    
    # 2. El sueco tiene un perro
    rest[2] = [ (N[(casa, "Sueco")] ~ M[(casa, "Perro")]) for casa in 1:5 ]
    
    # 3. El danés bebe té
    rest[3] = [ (N[(casa, "Danes")] ~ B[(casa, "Te")]) for casa in 1:5 ]
    
    # 4. La casa verde está inmediatamente a la izquierda de la casa blanca
    rest[4] = [[ (C[(casa, "Verde")] > C[(casa+1, "Blanco")]) for casa in 1:4 ] ;
             [!C[(1, "Blanco")]];  # La casa blanca no puede estar en la posición 1
             [!C[(5, "Verde")]]]   # La casa verde no puede estar en la posición 5
    
    # 5. El dueño de la casa verde bebe café
    rest[5] = [ (C[(casa, "Verde")] ~ B[(casa, "Cafe")]) for casa in 1:5 ]
    
    # 6. La persona que fuma Pall Mall tiene un pájaro
    rest[6] = [ (F[(casa, "PallMall")] ~ M[(casa, "Pajaro")]) for casa in 1:5 ]
    
    # 7. El dueño de la casa amarilla fuma Dunhill
    rest[7] = [ (C[(casa, "Amarillo")] ~ F[(casa, "Dunhill")]) for casa in 1:5 ]
    
    # 8. El hombre en la casa del medio bebe leche
    rest[8] = [B[(3, "Leche")]]  # La casa del medio (casa 3) bebe leche
    
    # 9. El noruego vive en la primera casa
    rest[9] = [N[(1, "Noruego")]]  # El noruego vive en la primera casa
    
    # 10. El hombre que fuma Blend vive al lado del que tiene un gato
    r10 = FormulaPL[]
    for casa in 1:5
        vecinos_gato = FormulaPL[]
        if casa > 1
            push!(vecinos_gato, M[(casa-1, "Gato")])
        end
        if casa < 5
            push!(vecinos_gato, M[(casa+1, "Gato")])
        end
        if length(vecinos_gato) > 0
            push!(r10, (F[(casa, "Blend")] > ⋁(vecinos_gato)))
        end
    end
    
    rest[10] = r10  # Asegurar que se cumple para todas las casas

    # 11. El hombre que tiene un caballo vive al lado del que fuma Dunhill
    r11 = FormulaPL[]
    for casa in 1:5
        vecinos_dunhill = FormulaPL[]
        if casa > 1
            push!(vecinos_dunhill, F[(casa-1, "Dunhill")])
        end
        if casa < 5
            push!(vecinos_dunhill, F[(casa+1, "Dunhill")])
        end
        if length(vecinos_dunhill) > 0
            push!(r11, (M[(casa, "Caballo")] > ⋁(vecinos_dunhill)))
        end
    end
    rest[11] = r11  # Asegurar que se cumple para todas las casas
    
    # 12. El hombre que fuma Blue Master bebe cerveza
    rest[12] = [ (F[(casa, "BlueMaster")] ~ B[(casa, "Cerveza")]) for casa in 1:5 ]

    # 13. El alemán fuma Prince
    rest[13] = [ (N[(casa, "Aleman")] ~ F[(casa, "Prince")]) for casa in 1:5 ]

    # 14. El noruego vive al lado de la casa azul
    # Como el noruego está en casa 1, la casa azul debe estar en casa 2
    rest[14] = [C[(2, "Azul")]]
    
    # 15. El hombre que fuma Blend vive al lado del que bebe agua
    r15 = FormulaPL[]
    for casa in 1:5
        vecinos_agua = FormulaPL[]
        if casa > 1
            push!(vecinos_agua, B[(casa-1, "Agua")])
        end
        if casa < 5
            push!(vecinos_agua, B[(casa+1, "Agua")])
        end
        if length(vecinos_agua) > 0
            push!(r15, (F[(casa, "Blend")] > ⋁(vecinos_agua)))
        end
    end
    rest[15] = r15  # Asegurar que se cumple para todas las casas
    
    Acertijo = reduce(vcat, [rest[i] for i in 1:15])
    #Acertijo = ⋀(restricciones_acertijo)

    return [Basicas ; Caracteristicas ; Acertijo]
end

# Función para visualizar la solución del acertijo de Einstein
function visual_sol_acertijo_einstein(solution_dict)
    println("\n" * "="^80)
    println("                    SOLUCIÓN DEL ACERTIJO DE EINSTEIN")
    println("="^80)
    
    # Crear estructura para almacenar la solución
    casas = [Dict{String, String}() for _ in 1:5]
    
    # Procesar la solución
    for (var, value) in solution_dict
        if value == 1
            # Parsear variables del tipo X(casa,caracteristica)
            if occursin(r"^[NCMBF]\(\d+,\w+\)$", var.name)
                tipo = var.name[1]
                contenido = var.name[3:end-1]
                partes = split(contenido, ",")
                casa = parse(Int, partes[1])
                caracteristica = string(partes[2])
                
                categoria = Dict('N' => "Nacionalidad", 'C' => "Color", 
                               'M' => "Mascota", 'B' => "Bebida", 'F' => "Cigarrillo")[tipo]
                casas[casa][categoria] = caracteristica
            end
        end
    end
    
    # Mostrar la tabla
    println("┌──────┬─────────────┬───────────┬──────────┬──────────┬─────────────┐")
    println("│ Casa │ Nacionalidad│   Color   │ Mascota  │  Bebida  │ Cigarrillo  │")
    println("├──────┼─────────────┼───────────┼──────────┼──────────┼─────────────┤")
    
    for casa in 1:5
        nac = get(casas[casa], "Nacionalidad", "?")
        col = get(casas[casa], "Color", "?")
        mas = get(casas[casa], "Mascota", "?")
        beb = get(casas[casa], "Bebida", "?")
        cig = get(casas[casa], "Cigarrillo", "?")
        
        println("│  $casa   │ $(rpad(nac, 11)) │ $(rpad(col, 9)) │ $(rpad(mas, 8)) │ $(rpad(beb, 8)) │ $(rpad(cig, 11)) │")
    end
    
    println("└──────┴─────────────┴───────────┴──────────┴──────────┴─────────────┘")
    
    # Encontrar y destacar quién tiene el pez
    println("\n" * "🐠 " * "="^25 * " RESPUESTA " * "="^25 * " 🐠")
    for casa in 1:5
        if get(casas[casa], "Mascota", "") == "Pez"
            nacionalidad = get(casas[casa], "Nacionalidad", "Desconocido")
            println("         ¡El $nacionalidad tiene el PEZ! (Casa #$casa)")
            break
        end
    end
    println("🐠 " * "="^61 * " 🐠")
    
    return casas
end

# Función principal para resolver el acertijo
function resolver_acertijo_einstein()
    println("🧠 Resolviendo el famoso Acertijo de Einstein...")
    println("   (También conocido como 'Zebra Puzzle')")

    println("\n⏳ Generando fórmula SAT...")
    formula = formula_acertijo_einstein()
    
    println("\n⏳ Ejecutando solucionador DPLL...")
    sat, sol = DPLL(formula)
    
    if sat == false
        println("❌ No se encontró solución. ¡Esto no debería pasar!")
        return false
    else
        println("✅ ¡Solución encontrada!")
        casas = visual_sol_acertijo_einstein(sol)
        return casas
    end
end

resolver_acertijo_einstein()


# ================================================================
# Problema de Horarios
# ================================================================

# Estructura para definir un curso
struct Curso
    nombre::String
    duracion::Int           # duración en bloques de tiempo
    profesor::String
    estudiantes::Vector{String}
    requiere_laboratorio::Bool
end

# Estructura para definir restricciones de disponibilidad
struct Disponibilidad
    entidad::String         # nombre del profesor o estudiante
    dia::String
    bloque::Int
    disponible::Bool
end

# Función principal para generar horarios
function formula_horarios(
    cursos::Vector{Curso},
    dias::Vector{String},
    bloques_por_dia::Int,
    aulas::Vector{String},
    laboratorios::Vector{String},
    disponibilidades::Vector{Disponibilidad} = Disponibilidad[]
)
    
    # Variables: H(curso, dia, bloque, aula) - el curso se imparte en ese 
    # día/bloque/aula
    H = Dict{Tuple{String, String, Int, String}, Var_PL}()
    
    # Generar todas las variables
    for c in cursos
        for d in dias
            for b in 1:bloques_por_dia
                # Si requiere laboratorio, solo usar laboratorios
                aulas_disponibles = c.requiere_laboratorio ? laboratorios : aulas
                for a in aulas_disponibles
                    H[(c.nombre, d, b, a)] = Var_PL("H($(c.nombre),$d,$b,$a)")
                end
            end
        end
    end
    
    restricciones = FormulaPL[]
    
    # RESTRICCIÓN 1: Cada curso debe programarse exactamente una vez
    for c in cursos
        slots_curso = Var_PL[]
        for d in dias
            for b in 1:(bloques_por_dia - c.duracion + 1)  # Debe caber la duración
                aulas_disponibles = c.requiere_laboratorio ? laboratorios : aulas
                for a in aulas_disponibles
                    push!(slots_curso, H[(c.nombre, d, b, a)])
                end
            end
        end
        push!(restricciones, Ex1(slots_curso))
    end
    
    # RESTRICCIÓN 2: No solapamiento de cursos en la misma aula
    for d in dias
        for a in aulas
            for b in 1:bloques_por_dia
                cursos_en_slot = Var_PL[]
                
                # Encontrar todos los cursos que podrían ocupar este slot
                for c in cursos
                    aulas_disponibles = c.requiere_laboratorio ? laboratorios : aulas
                    if a in aulas_disponibles
                        # El curso puede ocupar este bloque si empezó en este 
                        # bloque o en bloques anteriores
                        for i in max(1, b - c.duracion + 1):b
                            if i <= bloques_por_dia - c.duracion + 1
                                push!(cursos_en_slot, H[(c.nombre, d, i, a)])
                            end
                        end
                    end
                end
                
                # A lo sumo un curso en cada slot de aula
                if length(cursos_en_slot) > 1
                    push!(restricciones, ⋀([!(cursos_en_slot[i] & cursos_en_slot[j]) 
                                          for i in 1:length(cursos_en_slot) 
                                          for j in (i+1):length(cursos_en_slot)]))
                end
            end
        end
    end
    
    # RESTRICCIÓN 3: Profesores no pueden estar en dos lugares al mismo tiempo
    profesores = unique([c.profesor for c in cursos])
    for p in profesores
        cursos_profesor = [c for c in cursos if c.profesor == p]
        
        for d in dias
            for b in 1:bloques_por_dia
                cursos_en_slot = Var_PL[]
                
                for c in cursos_profesor
                    aulas_disponibles = c.requiere_laboratorio ? laboratorios : aulas
                    for a in aulas_disponibles
                        # El curso ocupa este bloque si empezó en este bloque 
                        # o antes
                        for i in max(1, b - c.duracion + 1):b
                            if i <= bloques_por_dia - c.duracion + 1
                                push!(cursos_en_slot, H[(c.nombre, d, i, a)])
                            end
                        end
                    end
                end
                
                # Un profesor no puede enseñar múltiples cursos simultáneamente
                if length(cursos_en_slot) > 1
                    push!(restricciones, ⋀([!(cursos_en_slot[i] & cursos_en_slot[j]) 
                                          for i in 1:length(cursos_en_slot) 
                                          for j in (i+1):length(cursos_en_slot)]))
                end
            end
        end
    end
    
    # RESTRICCIÓN 4: Estudiantes no pueden estar en dos cursos al mismo tiempo
    todos_estudiantes = unique(vcat([c.estudiantes for c in cursos]...))
    for e in todos_estudiantes
        cursos_estudiante = [c for c in cursos if e in c.estudiantes]
        
        for d in dias
            for b in 1:bloques_por_dia
                cursos_en_slot = Var_PL[]
                
                for c in cursos_estudiante
                    aulas_disponibles = c.requiere_laboratorio ? laboratorios : aulas
                    for a in aulas_disponibles
                        # El curso ocupa este bloque si empezó en este bloque 
                        # o antes
                        for i in max(1, b - c.duracion + 1):b
                            if i <= bloques_por_dia - c.duracion + 1
                                push!(cursos_en_slot, H[(c.nombre, d, i, a)])
                            end
                        end
                    end
                end
                
                # Un estudiante no puede estar en múltiples cursos simultáneamente
                if length(cursos_en_slot) > 1
                    push!(restricciones, ⋀([!(cursos_en_slot[i] & cursos_en_slot[j]) 
                                          for i in 1:length(cursos_en_slot) 
                                          for j in (i+1):length(cursos_en_slot)]))
                end
            end
        end
    end
    
    # RESTRICCIÓN 5: Respetar disponibilidades
    for d in disponibilidades
        if !d.disponible
            # Si no está disponible, no puede tener cursos en ese slot
            for c in cursos
                # Verificar si la entidad está relacionada con el curso
                relacionado = false
                if c.profesor == d.entidad
                    relacionado = true
                elseif d.entidad in c.estudiantes
                    relacionado = true
                end
                
                if relacionado
                    aulas_disponibles = c.requiere_laboratorio ? laboratorios : aulas
                    for a in aulas_disponibles
                        # El curso no puede ocupar este bloque si empezó en este 
                        # bloque o antes
                        for i in max(1, d.bloque - c.duracion + 1):d.bloque
                            if i <= bloques_por_dia - c.duracion + 1 && i >= 1
                                push!(restricciones, !H[(c.nombre, d.dia, i, a)])
                            end
                        end
                    end
                end
            end
        end
    end
    
    return restricciones
end

# Función para visualizar la solución de horarios
function visual_sol_horarios(
    solution_dict, 
    cursos::Vector{Curso},
    dias::Vector{String}, 
    bloques_por_dia::Int,
    aulas::Vector{String},
    laboratorios::Vector{String}
)
    println("\n" * "="^90)
    println("                                    HORARIO GENERADO")
    println("="^90)
    
    # Crear estructura del horario
    horario = Dict{Tuple{String, Int}, Tuple{String, String, String}}()  # (dia, bloque) => (curso, aula, profesor)
    
    # Procesar la solución
    for (var, value) in solution_dict
        if value == 1 && startswith(var.name, "H(")
            # Parsear H(curso,dia,bloque,aula)
            contenido = var.name[3:end-1]
            partes = split(contenido, ",")
            
            if length(partes) == 4
                curso_nombre = partes[1]
                dia = partes[2]
                bloque = parse(Int, partes[3])
                aula = partes[4]
                
                # Encontrar el curso para obtener información adicional
                curso_info = findfirst(c -> c.nombre == curso_nombre, cursos)
                if curso_info !== nothing
                    curso = cursos[curso_info]
                    
                    # Marcar todos los bloques que ocupa este curso
                    for b in bloque:(bloque + curso.duracion - 1)
                        if b <= bloques_por_dia
                            horario[(dia, b)] = (curso.nombre, aula, curso.profesor)
                        end
                    end
                end
            end
        end
    end
    
    # Mostrar horario por día
    for d in dias
        println("\n📅 $d")
        println("─"^90)
        
        # Cabecera de la tabla
        println("┌─────────┬─────────────────────────┬─────────────────┬────────────────────────┐")
        println("│ Bloque  │         Curso           │       Aula      │       Profesor         │")
        println("├─────────┼─────────────────────────┼─────────────────┼────────────────────────┤")
        
        for b in 1:bloques_por_dia
            if haskey(horario, (d, b))
                c, a, p = horario[(d, b)]
                tipo_aula = a in laboratorios ? "🔬 $a" : "🏫 $a"
                
                println("│  $b      │ $(rpad(c, 23)) │ $(rpad(tipo_aula, 15)) │ $(rpad(p, 22)) │")
            else
                println("│  $b      │ $(rpad("--- LIBRE ---", 23)) │ $(rpad("", 15)) │ $(rpad("", 22)) │")
            end
        end
        
        println("└─────────┴─────────────────────────┴─────────────────┴────────────────────────┘")
    end
    
    # Estadísticas
    println("\n📊 ESTADÍSTICAS:")
    cursos_programados = Set([c for ((d, b), (c, a, p)) in horario])
    println("   • Cursos programados: $(length(cursos_programados))/$(length(cursos))")
    
    # Utilización de aulas
    println("   • Utilización de aulas:")
    for a in vcat(aulas, laboratorios)
        uso = count(v -> v[2] == a, values(horario))
        total_slots = length(dias) * bloques_por_dia
        porcentaje = round(uso / total_slots * 100, digits=1)
        tipo = a in laboratorios ? "🔬" : "🏫"
        println("     $tipo $a: $uso/$total_slots slots ($porcentaje%)")
    end
    
    return horario
end

# Función para generar un reporte detallado por profesor
function reporte_profesores(horario, cursos::Vector{Curso}, dias::Vector{String})
    println("\n👨‍🏫 REPORTE POR PROFESOR:")
    println("="^60)
    
    profesores = unique([curso.profesor for curso in cursos])
    
    for profesor in profesores
        println("\n🎓 $profesor:")
        cursos_profesor = [curso.nombre for curso in cursos if curso.profesor == profesor]
        
        for dia in dias
            clases_dia = [(bloque, curso, aula) for ((d, bloque), (curso, aula, prof)) in horario 
                         if d == dia && prof == profesor]
            
            if !isempty(clases_dia)
                sort!(clases_dia)
                println("  📅 $dia:")
                for (bloque, curso, aula) in clases_dia
                    println("    • Bloque $bloque: $curso en $aula")
                end
            end
        end
    end
end

# Función de prueba con datos de ejemplo
function test_horarios_universidad()
    println("🏫 Probando sistema de horarios universitario...")
    
    # Definir cursos
    cursos = [
        Curso("Matemáticas I", 2, "Dr. García", ["Ana", "Luis", "María"], false),
        Curso("Física I", 2, "Dr. López", ["Ana", "Carlos", "Pedro"], false),
        Curso("Lab. Química", 3, "Dra. Martín", ["Luis", "María", "Pedro"], true),
        Curso("Programación", 2, "Dr. García", ["Carlos", "Ana"], false),
        Curso("Estadística", 1, "Dra. Ruiz", ["María", "Luis", "Pedro"], false)
    ]
    
    # Definir disponibilidad temporal
    dias = ["Lunes", "Martes", "Miércoles"]
    bloques_por_dia = 6
    aulas = ["Aula-101", "Aula-102", "Aula-201"]
    laboratorios = ["Lab-A", "Lab-B"]
    
    # Definir algunas restricciones de disponibilidad
    disponibilidades = [
        Disponibilidad("Dr. García", "Lunes", 1, false),     
            # No disponible primer bloque del lunes
        Disponibilidad("Ana", "Martes", 6, false),           
            # Ana no disponible último bloque del martes
        Disponibilidad("Dra. Martín", "Miércoles", 1, false) 
            # No disponible primer bloque del miércoles
    ]
    
    println("   📚 Cursos: $(length(cursos))")
    println("   🏫 Aulas regulares: $(length(aulas))")
    println("   🔬 Laboratorios: $(length(laboratorios))")
    println("   📅 Días: $(join(dias, ", "))")
    println("   ⏰ Bloques por día: $bloques_por_dia")
    
    # Generar y resolver
    formula = formula_horarios(cursos, dias, bloques_por_dia, aulas, laboratorios, disponibilidades)
    
    println("\n⏳ Generando fórmula SAT...")
    variables = Set([vars_of(f) for f in formula])
    println("   Variables generadas: $(length(variables))")
    
    println("\n⏳ Ejecutando solucionador DPLL...")
    sat, sol = DPLL(formula)
    
    if sat == false
        println("❌ No se pudo generar un horario válido con las restricciones dadas.")
        println("   Posibles causas:")
        println("   • Demasiados cursos para el tiempo disponible")
        println("   • Conflictos irresolubles de disponibilidad")
        println("   • Insuficientes aulas/laboratorios")
        return false
    else
        println("✅ ¡Horario generado exitosamente!")
        horario = visual_sol_horarios(sol, cursos, dias, bloques_por_dia, aulas, laboratorios)
        reporte_profesores(horario, cursos, dias)
        return horario
    end
end

# Función para crear un ejemplo más complejo
function test_horarios_complejo()
    println("🎓 Probando sistema de horarios complejo (Facultad de Ingeniería)...")
    
    cursos = [
        Curso("Cálculo I", 3, "Dr. Álvarez", ["Ana", "Luis", "Carlos", "María"], false),
        Curso("Álgebra", 2, "Dra. Pérez", ["Ana", "Pedro", "Sofía"], false),
        Curso("Física I", 3, "Dr. Gómez", ["Luis", "Carlos", "Pedro"], false),
        Curso("Lab. Física", 2, "Dr. Gómez", ["Luis", "Carlos", "Pedro"], true),
        Curso("Programación I", 2, "Dra. Torres", ["María", "Sofía", "Ana"], false),
        Curso("Lab. Programación", 2, "Dra. Torres", ["María", "Sofía", "Ana"], true),
        Curso("Química", 2, "Dr. Morales", ["Carlos", "Pedro", "Sofía"], false),
        Curso("Lab. Química", 3, "Dr. Morales", ["Carlos", "Pedro", "Sofía"], true)
    ]
    
    dias = ["Lunes", "Martes", "Miércoles", "Jueves", "Viernes"]
    bloques_por_dia = 8
    aulas = ["Aula-A", "Aula-B", "Aula-C", "Aula-D"]
    laboratorios = ["Lab-Comp", "Lab-Física", "Lab-Química"]
    
    disponibilidades = [
        Disponibilidad("Dr. Álvarez", "Viernes", 7, false),
        Disponibilidad("Dr. Álvarez", "Viernes", 8, false),
        Disponibilidad("Dra. Torres", "Lunes", 1, false),
        Disponibilidad("Ana", "Miércoles", 8, false),
        Disponibilidad("Pedro", "Jueves", 1, false)
    ]
    
    formula = formula_horarios(cursos, dias, bloques_por_dia, aulas, laboratorios, disponibilidades)
    
    println("⏳ Resolviendo horario complejo...")
    sat, sol = DPLL(formula)
    
    if sat
        println("✅ ¡Horario complejo resuelto!")
        horario = visual_sol_horarios(sol, cursos, dias, bloques_por_dia, aulas, laboratorios)
        return horario
    else
        println("❌ No se pudo resolver el horario complejo")
        return false
    end
end

# ======= EJECUTAR EJEMPLOS =======
println("🚀 Iniciando pruebas del sistema de horarios...\n")

# Ejemplo básico
resultado1 = test_horarios_universidad()

println("\n" * "="^90)

# Ejemplo complejo
resultado2 = test_horarios_complejo()

# ============= Asignacio de Trabajadores a Tareas =============
#=
Un problema muy común en gestión empresarial es la asignación óptima de 
trabajadores a tareas (AT). En este problema:

- Tenemos un grupo, W, de trabajadores, cada uno con un conjunto de 
   habilidades específicas, H_w.
- Tenemos un conjunto de tareas, T, cada una requiere ciertas habilidades 
   para ser completada.
- Cada tarea debe ser asignada a exactamente un trabajador.
- Solo se puede asignar un trabajador a una tarea si posee todas las 
   habilidades requeridas.
- Hay incompatibilidades entre diversas tareas (por ejemplo, testing y deploy 
   no deberían ser ejecutadas por el mismo trabajador).

Variables proposicionales:
- A(w,t) = 1 si y solo si el trabajador w es asignado a la tarea t.

Restricciones:
1. Cada tarea se asigna a exactamente un trabajador:
   ⋀_{t ∈ T} ∃!({A(w,t)}_{w ∈ W})
3. Solo asignaciones válidas: ⋀_{w,t} (A(w,t) → H_w(t)).
4. Sin incompatibilidades: un mismo trabajador no puede realizar dos tareas 
   que sean incompatibles entre sí.

Este enfoque es más realista ya que modela las limitaciones de recursos 
humanos en proyectos reales.
=#

function formula_AT(A, W::Vector{String}, T::Vector{String}, 
                                         H::Dict{String, Vector{String}},
                                         I::Vector{Tuple{String, String}} = [])
    
    # Restricción 1: Cada trabajador realiza exactamente una tarea
    trabajador_tarea(w) = Ex1([A[(w, t)] for t in T if t in H[w]])
    Trabajadores = [trabajador_tarea(w) for w in W]
    
    # Restricción 2: Cada tarea es realizada por exactamente un trabajador
    tarea_trabajador(t) = Ex1([A[(w, t)] for w in W if t in H[w]])
    Tareas = [tarea_trabajador(t) for t in T]
    
    # Restricción 3: Solo asignar tareas para las que el trabajador tiene 
    # habilidades
    Habilidades_validas = FormulaPL[]
    for w in W
        for t in T
            if !(t in H[w])
                push!(Habilidades_validas, !A[(w, t)])
            end
        end
    end
    Habilidades = Habilidades_validas
    
    # Restricción 4: Incompatibilidades (tareas que no pueden ser hechas por el 
    # mismo trabajador)
    Incompatibles = FormulaPL[]
    for (t1, t2) in I
        for w in W
            if t1 in H[w] && t2 in H[w]
                push!(Incompatibles, !(A[(w, t1)] & A[(w, t2)]))
            end
        end
    end
    Incompatibilidad = Incompatibles

    return [Trabajadores ; Tareas ; Habilidades ; Incompatibilidad]
end

function resolver_asignacion_trabajadores()
    # Definir trabajadores y tareas
    trabajadores = ["Ana", "Bob", "Carlos", "Diana"]
    tareas = ["Programación", "Testing", "Documentación", "Deploy"]
    
    # Definir habilidades de cada trabajador
    habilidades = Dict(
        "Ana" => ["Programación", "Testing"],
        "Bob" => ["Programación", "Deploy"],
        "Carlos" => ["Testing", "Documentación", "Deploy"],
        "Diana" => ["Documentación", "Deploy"]
    )
   
    # Incompatibilidades: Testing y Deploy no pueden ser hechos por la misma
    # persona
    # (por ejemplo, por políticas de calidad)
    incompatibilidades = [("Testing", "Deploy")]
    
    # Crear variables proposicionales T[(trabajador, tarea)]
    A = Dict()
    for w in trabajadores
        for t in tareas
            A[(w, t)] = Var_PL("$(w)_$(t)")
        end
    end
    
    # Crear la fórmula
    formula = formula_AT(A, trabajadores, tareas, habilidades, incompatibilidades)
    println("Fórmula generada:")
    println(formula)
    
    println("Variables del problema:")
    for (k, v) in A
        println("  $(v.name) = $(k[1]) realiza $(k[2])")
    end
    println()
    
    # Resolver
    sat, solucion = DPLL(formula)
  
    if sat
        println("-"^30)
        println("Asignación encontrada:")
        println("-"^30)
        for w in trabajadores
            for t in tareas
                v = A[(w, t)]
                if solucion[v]
                    println("  $w → $t")
                end
            end
        end
    else
        println("No hay solución posible con estas restricciones")
    end
    
    return solucion
end

resolver_asignacion_trabajadores();

# ============= Sistema Experto Eléctrico =============
#=
Caso: Diagnóstico de fallos en un sistema técnico (Sistema Experto)
Contexto: Se quiere diagnosticar fallos en un sistema eléctrico industrial. 
   El técnico introduce información observada, y el sistema debe deducir 
   posibles causas.

Hechos y reglas (simplificados pero no triviales):

Variables proposicionales (Var_PL):

p: Hay corriente en el sistema
b: El breaker está activado
f: El fusible está fundido
s: El sensor muestra actividad
a: La alarma está activada
r: El relé está cerrado
l: Hay luz en el panel

Conocimiento (conjunto Γ de fórmulas):

b → p — Si el breaker está activado, hay corriente
¬f → p — Si el fusible no está fundido, hay corriente
(p ∧ r) → l — Si hay corriente y el relé está cerrado, hay luz
p → s — Si hay corriente, el sensor muestra actividad
¬p → a — Si no hay corriente, se activa la alarma
l → ¬a — Si hay luz, no hay alarma
a → ¬s — Si hay alarma, el sensor no muestra actividad

Objetivo: Dado un conjunto de observaciones (hechos actuales), deducir qué 
falla(s) son compatibles o necesarias, o si hay contradicción.

=#

# Variables
p, b, f, s, a, r, l = vars("p", "b", "f", "s", "a", "r", "l")

# Base de conocimiento (reglas del sistema)
Γ = [
    b > p,                 # breaker → corriente
    -f > p,                # no fusible quemado → corriente
    (p & r) > l,           # corriente y relé → luz
    p > s,                 # corriente → sensor activo
    -p > a,                # no corriente → alarma
    l > -a,                # luz → no alarma
    a > -s                 # alarma → no sensor activo
]

println("Base de conocimiento cargada.")

# -----------------------------
# Caso 1: Observaciones
# -----------------------------
# Observaciones:
# - Hay alarma (a)
# - No hay luz (¬l)
# - El breaker está activado (b)

observaciones = [a, -l, b]

# Pregunta: ¿Se deduce que el fusible está fundido?
φ = f

# ¿Γ ∪ observaciones ⊨ f?
println("\n¿Se deduce que el fusible está fundido?")
se_deduce = DPLL_LC(vcat(Γ, observaciones), φ)
println("Resultado: ", se_deduce)

# Alternativa: ¿Cuáles son los modelos compatibles con las observaciones + base?
modelos = models(vcat(Γ, observaciones))

println("\nModelos compatibles con las observaciones:")
for m in modelos
    println(m)
end

# -----------------------------
# Caso 2: ¿Contradicción?
# -----------------------------
# Introducimos ahora que el sensor muestra actividad (s)

observaciones2 = [a, -l, b, s]

println("\n¿Hay contradicción si también se observa sensor activo?")
contradiccion = UNSAT(⋀(vcat(Γ, observaciones2)))
println("¿Contradicción?: ", contradiccion)

#=
Comentarios:
* Este sistema experto no podría resolverse cómodamente a mano por el número 
   de combinaciones (7 variables → 128 posibles mundos).
* Se analiza si ciertas conclusiones (como f) son necesarias dada la evidencia.
* También se detectan observaciones inconsistentes con el conocimiento 
   (observaciones contradictorias).
=#

# ============= Sistema Experto Médico =============

# sistema_experto_diagnostico.jl
# --------------------------------------------
# Sistema experto proposicional para diagnóstico médico simple

# =====================
# VARIABLES NOMBRADAS
# =====================
# Enfermedades
asma      = Var_PL("asma")
gripe     = Var_PL("gripe")
covid     = Var_PL("covid")
alergia   = Var_PL("alergia")

# Síntomas
tos       = Var_PL("tos")
fiebre    = Var_PL("fiebre")
mialgia   = Var_PL("mialgia")
disnea    = Var_PL("disnea")
estornudo = Var_PL("estornudo")

# Antecedentes
fumador   = Var_PL("fumador")
asma_prev = Var_PL("asma_prev")

# Tratamientos
responde_antivirales = Var_PL("responde_antivirales")
responde_bronco      = Var_PL("responde_bronco")

# Riesgo
riesgo = Var_PL("riesgo")

# =====================
# BASE DE CONOCIMIENTO
# =====================

Γ = [
    # Reglas de síntomas comunes
    tos & fiebre       > gripe,
    fiebre & mialgia   > covid,
    tos & estornudo    > alergia,
    disnea & fiebre    > asma,

    # Reglas de antecedentes
    fumador & disnea   > asma,
    asma_prev & tos    > asma,

    # Población de riesgo
    riesgo > covid,
    riesgo > asma,

    # Diagnóstico implica respuesta a tratamiento
    covid  > responde_antivirales,
    asma   > responde_bronco,

    # Síntomas incompatibles
    estornudo & mialgia > -alergia,
    disnea & estornudo  > -gripe
]

# ===========================================
# OBSERVACIONES DEL PACIENTE
# ===========================================

observaciones = [
    tos,
    fiebre,
    disnea,
    fumador,
    riesgo
]

# ===========================================
# INFERENCIAS
# ===========================================

# ¿Se deduce que tiene asma?
println("¿El paciente tiene asma?: ", DPLL_LC(vcat(Γ, observaciones), asma))

# ¿Se deduce que tiene covid?
println("¿El paciente tiene covid?: ", DPLL_LC(vcat(Γ, observaciones), covid))

# ¿Modelos compatibles con las observaciones?
println("\nModelos compatibles:")
for m in models(vcat(Γ, observaciones))
    println(m)
end

# ¿Contradicción si decimos que NO responde a broncodilatadores?
println("\n¿Contradicción si ¬responde_bronco?: ",
    UNSAT(⋀(vcat(Γ, observaciones, [-responde_bronco]))))
