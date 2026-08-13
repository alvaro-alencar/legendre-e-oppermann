# 🧪 Math Lab: Legendre e Oppermann

Laboratório numérico e formalização parcial das conjecturas de Legendre e Oppermann.

## Status científico

Este repositório não declara uma prova das conjecturas. A configuração padrão usa `N_STEP = 10_000`, portanto o scan é amostral. Para percorrer todos os inteiros do intervalo configurado, use `N_STEP = 1`.

## Implementação corrigida

Os dois pontos de entrada numéricos são:

- `Analise_Primos_Legendre.py`
- `Analise_Primos_Legendre.ipynb`

O notebook foi regenerado para refletir a fórmula explícita corrigida e a distinção entre scan amostral e exaustivo.

Para `rho = 1/2 + i gamma`, a contribuição `Re(x^rho / rho)` usa o denominador correto `0.25 + gamma^2`. A versão anterior dividia pela raiz dessa quantidade.

O preditor continua sendo truncado e condicionado à linha crítica, pois representa os zeros como `rho = 1/2 + i gamma`. Portanto, ele não é um teste independente da Hipótese de Riemann. A conversão `Delta psi / log x` em quantidade prevista de primos também é heurística, porque `psi` inclui potências de primos.

## Kernel de Esmeralda em Lean

A pasta `proof/` inicia a formalização incremental.

O módulo `proof/KernelEsmeralda/Detection.lean` contém o teorema `clean_detection`: se uma quantidade `deltaPsi` se decompõe exatamente em massa de primos mais massa de potências superiores, e `deltaPsi` domina toda a contribuição das potências superiores, então existe um primo entre `n²` e `(n+1)²`.

Isso corrige a passagem inválida de `Delta psi > 0` diretamente para a existência de primo.

A próxima etapa é ligar essa decomposição abstrata à diferença real da função de Chebyshev e depois formalizar o controle espectral do Kernel de Esmeralda.

## Resultados históricos

`overview.png` e `analysis.png` pertencem à rodada anterior à correção. O script corrigido gera novos gráficos com sufixo `_corrected`.

## Autor

Álvaro Alencar
