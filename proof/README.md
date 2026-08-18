# Kernel de Esmeralda em Lean

Esta pasta transforma o programa de ataque à Conjectura de Legendre em uma cadeia de lemas auditáveis. O CI instala Lean/Lake e executa `lake build` no pull request.

## Estado formal atual

A formalização usa `Chebyshev.psi`, `Chebyshev.theta` e a função de von Mangoldt da Mathlib. Entre os passos já kernel-checked estão:

- `Δψ = Δθ + Δ(ψ-θ)`;
- `Δθ > 0` implica um primo estritamente entre `n²` e `(n+1)²`;
- `Δψ(n)` é exatamente a soma de von Mangoldt em `(n²,(n+1)²]`;
- `ψ(n+1)-ψ(n)=Λ(n+1)≤log(n+1)`;
- as desigualdades de Costa–Pereira dão uma cota local explícita para a contribuição das potências superiores;
- para `K≤1`, `emeraldMass(K,n)≤Δψ(n)`;
- existem minorantes suaves, entre `0` e `1`, com suporte estritamente em `(log n², log (n+1)²)`;
- com `k(u)=exp(u/2)K(u)`, o fator `1/√m` do lado primo de Weil cancela exatamente;
- o teste complexo é `C²` e de suporte compacto;
- a soma prima infinita na normalização de Weil reduz-se exatamente a `emeraldMass`;
- pode-se escolher um núcleo interno cuja contribuição exponencial é exatamente `n`, produzindo a cota `n ≤ Re(P_K)` para o termo dos polos.

## Barreira aritmética explícita

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

## Fórmula explícita concreta da zeta

O pacote fixa como dependência o repositório público `anthropics/zeta-23-lean` no commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, usando a mesma revisão da Mathlib.

`Zeta23Bridge.lean` importa a instância sem hipóteses `EF_lit zetaZeroConfig` e prova que ela produz exatamente o balanço usado pelo Kernel de Esmeralda. Também expõe a convergência absoluta da série de zeros para o nosso teste.

Assim, a fórmula explícita deixou de ser uma hipótese própria deste projeto.

## Fronteira atual

Para cada `n ≥ 2`, o Lean já constrói um peso admissível `K` para o qual basta provar a desigualdade concreta

```text
B(n) - n < Re(G_K - Z_K),
```

onde `G_K` é o termo arquimediano e `Z_K` é a soma, com multiplicidades, sobre os zeros não triviais reais da função zeta de Riemann na formalização do `Zeta23`.

Esse é agora o gargalo matemático. A próxima fase é obter estimativas quantitativas para `G_K` e, sobretudo, cancelamento suficiente em `Z_K`. Convergência absoluta por si só não fornece esse cancelamento.

Nada nesta pasta afirma que a Conjectura de Legendre foi provada. A finalidade é tornar explícito, kernel-check após kernel-check, exatamente o que já foi demonstrado e o que ainda falta.
