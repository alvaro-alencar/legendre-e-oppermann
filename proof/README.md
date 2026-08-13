# Kernel de Esmeralda em Lean

Esta pasta separa a camada formal da camada experimental do repositório. O objetivo é transformar a tentativa sobre a Conjectura de Legendre em uma cadeia de lemas auditáveis, deixando explícito onde termina o que já foi provado e onde começa o gargalo analítico.

## Estado atual

A formalização usa diretamente as definições de `Chebyshev.psi` e `Chebyshev.theta` da Mathlib. O CI instala Lean/Lake e executa `lake build` a cada pull request para `main`.

Módulos compilados:

- `KernelEsmeralda/DetectionCore.lean`: detecção elementar a partir de massa logarítmica positiva de primos;
- `KernelEsmeralda/ChebyshevBridge.lean`: define `Δψ`, `Δθ` e `ψ-θ`, e prova a identidade exata `Δψ = Δθ + Δ(ψ-θ)`;
- `KernelEsmeralda/PrimeFromThetaCore.lean`: prova que `Δθ > 0` implica a existência de um primo estritamente entre `n²` e `(n+1)²`;
- `KernelEsmeralda/LegendreCriterion.lean`: transforma dominância de `Δψ` sobre a contribuição das potências superiores em um critério suficiente para Legendre.

Em particular, a formalização já elimina um erro lógico importante: **`Δψ > 0` sozinho não basta**, porque `ψ` também conta potências de primos.

## Próximo gargalo

A próxima etapa é localizar a contribuição de `ψ-θ` dentro da própria janela quadrática. A cota global da Mathlib,

`ψ(x) - θ(x) = O(√x)`, 

é rigorosa mas grosseira demais para um intervalo de comprimento `2n+1`. O alvo agora é uma cota local para

`[ψ((n+1)²)-θ((n+1)²)] - [ψ(n²)-θ(n²)]`.

Depois disso, o problema realmente difícil fica isolado: obter uma cota inferior suficientemente forte para `Δψ`, o ponto em que entram a fórmula explícita, os zeros da zeta e a proposta do Kernel de Esmeralda.

Nada nesta pasta, no estado atual, afirma que a Conjectura de Legendre foi provada.
