# 🧪 Math Lab: Legendre e Oppermann

Laboratório computacional para explorar numericamente a **Conjectura de Legendre** e a **Conjectura de Oppermann**, além de comparar a contagem exata de primos com um preditor heurístico baseado em uma forma truncada da fórmula explícita de Riemann.

## ⚠️ Status científico

Este repositório contém **experimentos numéricos**, não uma prova das conjecturas.

Na configuração padrão atual:

```python
N_START = 10_000
N_END   = 1_000_000
N_STEP  = 10_000
```

o programa testa apenas os valores efetivamente percorridos por esse passo. Portanto, o experimento padrão é **amostral**: ele não verifica todos os inteiros até `1_000_000`.

A implementação corrigida e atualmente autoritativa é:

```text
Analise_Primos_Legendre.py
```

O arquivo antigo `Analise_Primos_Legendre.ipynb` é preservado como artefato legado e não deve ser usado como referência científica até ser regenerado a partir da versão corrigida.

## 🎯 O que é testado

### Conjectura de Legendre

Para cada inteiro positivo `n`, a conjectura afirma que existe pelo menos um primo no intervalo

\[
n^2 < p < (n+1)^2.
\]

No código, a contagem exata é obtida com `sympy.primepi`.

### Conjectura de Oppermann

Para `n > 1`, a conjectura requer pelo menos um primo em cada uma das duas metades:

\[
n^2 < p < n(n+1)
\]

and

\[
n(n+1) < q < (n+1)^2.
\]

O programa testa essas duas condições separadamente.

## 🔬 Preditor pela fórmula explícita

O projeto também usa um preditor exploratório baseado em uma soma truncada sobre zeros não triviais da função zeta.

Para `rho = 1/2 + i gamma`, a contribuição real correta é

\[
\operatorname{Re}\left(\frac{x^\rho}{\rho}\right)
=
\frac{\sqrt{x}\left(\frac12\cos(\gamma\log x)+\gamma\sin(\gamma\log x)\right)}{\frac14+\gamma^2}.
\]

A versão anterior dividia por `sqrt(1/4 + gamma^2)`. Isso foi corrigido para o denominador correto `1/4 + gamma^2`.

### Limitação importante

`mpmath.zetazero(k)` fornece as ordenadas `gamma` dos zeros conhecidos na linha crítica, e o modelo numérico os representa como

\[
\rho = \frac12 + i\gamma.
\]

Logo, esse preditor é **truncado e condicionado à linha crítica**. Ele não pode ser usado como evidência independente para a Hipótese de Riemann.

Além disso, a transformação

\[
\Delta\psi / \log x
\]

em uma estimativa da quantidade de primos é heurística: `psi(x)` pesa primos por `log p` e também inclui potências de primos.

## 📊 Sobre os resultados existentes

Os arquivos `overview.png` e `analysis.png` pertencem à rodada histórica anterior à correção da fórmula explícita. Eles são mantidos para registro, mas **não devem ser tratados como resultados da implementação corrigida**.

Ao executar `Analise_Primos_Legendre.py`, novos gráficos são gerados como:

```text
overview_corrected.png
analysis_corrected.png
```

## 🛠️ Stack

- Python 3.10+
- NumPy
- Numba
- SymPy
- mpmath
- Matplotlib
- tqdm

## 🚀 Como executar

```bash
pip install -r requirements.txt
python Analise_Primos_Legendre.py
```

A configuração fica no dicionário `CONFIG` no início do arquivo.

Se `N_STEP = 1`, o programa percorre todos os inteiros do intervalo configurado. Isso pode ser computacionalmente muito mais caro, especialmente porque `primepi` é chamado repetidamente em valores da ordem de `n^2`.

## 🧭 Próxima etapa: do experimento à prova

A camada numérica deve ser separada da eventual tentativa de prova formal. Um caminho natural é criar uma pasta `proof/` para formalizar, em ordem:

1. a decomposição de `psi((n+1)^2) - psi(n^2)`;
2. a separação rigorosa entre contribuições de primos e potências de primos;
3. o Kernel de Esmeralda e suas propriedades analíticas;
4. a cota efetiva do termo envolvendo os zeros da zeta;
5. somente então, qualquer conclusão assintótica sobre Legendre ou Oppermann.

O objetivo científico correto é localizar exatamente o primeiro lema que pode ser provado com rigor, e não antecipar a conclusão.

## 👨‍💻 Autor

**Álvaro Alencar**

Fundador da Vortex Development | Curador de IA
