# Kernel de Esmeralda em Lean

Esta pasta inicia a formalização do programa ligado à Conjectura de Legendre.

O arquivo `KernelEsmeralda/Detection.lean` formaliza o primeiro portão lógico:

- `primesBetweenSquares n` reúne os primos entre `n²` e `(n+1)²`;
- `primeMass n` soma `log p` sobre esses primos;
- `clean_detection` mostra que, se `deltaPsi = primeMass n + higherPowerMass` e `deltaPsi > higherPowerMass`, então existe um primo no intervalo.

Isso evita confundir positividade de `Delta psi` com existência imediata de primo, pois a função de Chebyshev também registra potências de primos.

Próximas etapas:

1. ligar `deltaPsi` à diferença real da função de Chebyshev;
2. separar exatamente primos e potências superiores;
3. majorar a contribuição das potências superiores;
4. formalizar o Kernel de Esmeralda e sua fórmula explícita;
5. controlar rigorosamente o termo espectral vindo dos zeros da zeta.

O item 5 permanece o gargalo principal. Esta pasta ainda não afirma uma prova da Conjectura de Legendre.
