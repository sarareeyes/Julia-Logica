# ==============================================================================
# Examen de LITI - Parte de Julia
# Curso 2025-2026
# Fecha: 7 de noviembre de 2025
# ==============================================================================

# 1: Rellena los siguientes datos:

#------------------------------------------------------------------------------
#
# Nombre y apellidos: Sara Reyes Merino
#
# DNI: 77869899H
#
#------------------------------------------------------------------------------

#===============================================================================
2: Enunciado del ejercicio propuesto:

Haciendo uso de la librería de Lógica Proposicional desarrollada para el curso 
en Julia, formaliza los siguientes hechos y reglas:

Σ = "o el testigo no dice la verdad o Juan estaba en la casa antes de cometerse
el crimen. Si Juan estaba en la casa antes de cometerse el crimen, vio al 
criminal. Si vio al criminal, sabe que no pudo ser el mayordomo".

A continuación:
1. Pasa todas las fórmulas de Σ a FNC.
2. Calcula una forma clausal de Σ.
3. Comprueba si podemos deducir que "si el testigo dice la verdad, Juan vio al 
criminal y sabe que no pudo ser el mayordomo" a partir de Σ aplicando el método 
que quieras.

===============================================================================#

# ==============================================================================
# 3: Solución:
p="el testigo dice la verdad"
q="Juan estaba en la casa antes de cometerse el crimen"
r="Juan vio al criminal"
s="Juan sabe que no pudo ser el mayordomo"
p, q, r, s = vars(:p, :q, :r, :s)
f=(-p|q)&(q>r)&(r>s)
f |> to_CNF # 1. FNC de f

g = ((p | q) & (-p | r) & (-q | -r))&(p>(r&s))
cl = f |> to_CF
DPLL(cl)

