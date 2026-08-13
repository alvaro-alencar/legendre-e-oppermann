# Kernel de Esmeralda em Lean

Esta pasta transforma a tentativa sobre a Conjectura de Legendre em uma cadeia de lemas auditáveis. O CI instala Lean/Lake e executa `lake build` no pull request.

## Estado formal atual

A formalização usa `Chebyshev.psi`, `Chebyshev.theta` e a função de von Mangoldt da Mathlib. Já estão kernel-checked:

- `Δψ = Δθ + Δ(ψ-θ)`;
- `Δθ > 0` implica um primo estritamente entre `n²` e `(n+1)²`;
- `Δψ(n)` é exatamente a soma de von Mangoldt em `(n²,(n+1)²]`;
- `ψ(n+1)-ψ(n)=Λ(n+1)≤log(n+1)`;
- as desigualdades de Costa–Pereira dão uma cota local explícita para a contribuição das potências superiores;
- para um peso `K≤1`, a massa ponderada `emeraldMass(K,n)` satisfaz `emeraldMass(K,n)≤Δψ(n)`;
- existe um minorante `C∞`, entre `0` e `1`, suportado estritamente em `(log n², log (n+1)²)`;
- com `k(u)=exp(u/2)K(u)`, o fator `1/√m` do lado primo de Weil cancela exatamente;
- o teste complexo resultante é `C²` e de suporte compacto;
- o ramo refletido `k(-log m)` é zero e a soma prima infinita inteira na normalização de Weil reduz-se exatamente a `emeraldMass`.

## Barreira explícita

Definimos

```text
B(n) = log(n+1)
     + (log 4 + 4) * ((n+1)²)^(1/3)
     + (log 4 + 4) * ((n+1)²)^(1/5).
```

O Lean verifica `Δ(ψ-θ)(n) ≤ B(n)` e, consequentemente,

```text
B(n) < emeraldMass(K,n)
    ⇒ existe primo p com n² < p < (n+1)².
```

## Gargalo atual

A camada aritmética e o lado primo estão isolados. O passo difícil restante é aplicar uma fórmula explícita de Weil ao teste esmeralda e controlar rigorosamente o lado espectral/arquimediano para obter uma cota inferior que force `emeraldMass(K,n) > B(n)`.

A infraestrutura pública de `zeta-23-lean` contém uma fórmula explícita de Weil para a zeta e usa a mesma revisão da Mathlib, mas ainda não foi incorporada como dependência deste pacote.

Nada nesta pasta afirma que a Conjectura de Legendre foi provada.
