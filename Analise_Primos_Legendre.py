#!/usr/bin/env python3
"""
Math Lab: verificação numérica amostral de Legendre e Oppermann.

IMPORTANTE
- Este programa faz verificação computacional dos valores de n efetivamente percorridos.
- Com N_STEP > 1, o resultado é AMOSTRAL, não uma verificação exaustiva até N_END.
- A aproximação por fórmula explícita usa apenas um número finito de zeros fornecidos por
  mpmath e representa cada zero como rho = 1/2 + i*gamma. Portanto, esse preditor é
  truncado e condicionado à linha crítica; ele não é evidência independente para RH.
- Nenhum resultado numérico produzido aqui constitui prova de Legendre ou Oppermann.
"""

import json
import os
import pickle
import time
from datetime import datetime

import matplotlib.pyplot as plt
import mpmath
import numpy as np
from numba import jit
from sympy import primepi
from tqdm import tqdm

CONFIG = {
    "N_START": 10_000,
    "N_END": 1_000_000,
    "N_STEP": 10_000,  # amostragem; use 1 apenas se quiser percorrer cada n
    "NUM_ZEROS": 500,
    "CHECKPOINT_INTERVAL": 100,
    "OUTPUT_DIR": "results_1M",
    "CACHE_FILE": "gammas_500_cache.npy",
}


def scan_is_exhaustive(config):
    """True somente quando todos os inteiros de N_START a N_END são percorridos."""
    return config["N_STEP"] == 1


def load_or_compute_zeros(num_zeros, cache_file):
    """Carrega ordinadas gamma dos zeros calculados por mpmath ou cria o cache."""
    if os.path.exists(cache_file):
        gammas = np.load(cache_file)
        if len(gammas) >= num_zeros:
            return gammas[:num_zeros]

    print(f"Computando {num_zeros} zeros da zeta para o preditor truncado...")
    gammas = np.array(
        [float(mpmath.zetazero(k).imag) for k in tqdm(range(1, num_zeros + 1))],
        dtype=np.float64,
    )
    np.save(cache_file, gammas)
    return gammas


@jit(nopython=True)
def chebyshev_psi_explicit(x, gammas):
    """Aproxima psi(x) pela fórmula explícita truncada.

    Para rho = 1/2 + i*gamma,

        Re(x^rho / rho)
        = sqrt(x) * (0.5*cos(gamma log x) + gamma*sin(gamma log x))
          / (0.25 + gamma^2).

    A soma usa os pares conjugados através do fator 2.
    Termos triviais e o termo -1/2 log(1-x^-2) são omitidos aqui porque o objetivo
    desta rotina é um preditor exploratório, não uma avaliação rigorosa de psi(x).
    """
    result = x - np.log(2.0 * np.pi)
    log_x = np.log(x)
    sqrt_x = np.sqrt(x)

    for gamma in gammas:
        rho_abs_sq = 0.25 + gamma * gamma
        phase = gamma * log_x
        numerator_real = sqrt_x * (
            0.5 * np.cos(phase) + gamma * np.sin(phase)
        )
        contribution = 2.0 * numerator_real / rho_abs_sq
        result -= contribution

    return result


@jit(nopython=True)
def compute_delta_psi(lower, upper, gammas):
    return chebyshev_psi_explicit(upper, gammas) - chebyshev_psi_explicit(lower, gammas)


def create_results_structure():
    return {
        "config": CONFIG.copy(),
        "timestamp_start": datetime.now().isoformat(),
        "timestamp_end": None,
        "n": [],
        "I1_real_count": [],
        "I1_predicted": [],
        "I1_error": [],
        "I1_relative_error": [],
        "I2_real_count": [],
        "I3_real_count": [],
        "legendre_holds": [],
        "oppermann_holds": [],
        "computation_time": [],
        "cumulative_legendre_success": [],
        "cumulative_oppermann_success": [],
    }


def analyze_single_n(n, gammas, primepi_func=primepi):
    """Testa Legendre e as duas metades de Oppermann para um único n."""
    start_time = time.time()

    a = n * n
    b = n * (n + 1)
    c = (n + 1) ** 2

    # Ground truth exato via pi(x).
    I1_real = int(primepi_func(c) - primepi_func(a))
    I2_real = int(primepi_func(b) - primepi_func(a))
    I3_real = int(primepi_func(c) - primepi_func(b))

    # Preditor heurístico baseado em Delta psi. Como log p varia pouco no intervalo,
    # dividimos pela escala log do centro geométrico. Isso NÃO é uma identidade exata.
    delta_psi = compute_delta_psi(a, c, gammas)
    log_scale = np.log(np.sqrt(a * c))
    I1_predicted = delta_psi / log_scale

    I1_error = abs(I1_predicted - I1_real)
    I1_rel_error = (100.0 * I1_error / I1_real) if I1_real > 0 else np.nan

    legendre_holds = I1_real > 0
    # Para n > 1, os pontos a, b, c são compostos; as duas condições abaixo
    # são a forma computacional usual da conjectura de Oppermann.
    oppermann_holds = (I2_real > 0) and (I3_real > 0)

    return {
        "n": n,
        "I1_real_count": I1_real,
        "I1_predicted": float(I1_predicted),
        "I1_error": float(I1_error),
        "I1_relative_error": float(I1_rel_error),
        "I2_real_count": I2_real,
        "I3_real_count": I3_real,
        "legendre_holds": legendre_holds,
        "oppermann_holds": oppermann_holds,
        "computation_time": time.time() - start_time,
    }


def save_checkpoint(results, output_dir, checkpoint_num):
    os.makedirs(output_dir, exist_ok=True)
    path = os.path.join(output_dir, f"checkpoint_{checkpoint_num:04d}.pkl")
    with open(path, "wb") as f:
        pickle.dump(results, f)
    return path


def save_final_results(results, output_dir):
    os.makedirs(output_dir, exist_ok=True)
    with open(os.path.join(output_dir, "results_final.pkl"), "wb") as f:
        pickle.dump(results, f)

    metadata = {
        "config": results["config"],
        "timestamp_start": results["timestamp_start"],
        "timestamp_end": results["timestamp_end"],
        "total_points": len(results["n"]),
        "scan_exhaustive_over_configured_range": scan_is_exhaustive(results["config"]),
        "explicit_formula_model": "truncated_RH_conditioned_predictor",
        "legendre_success_rate": results["cumulative_legendre_success"][-1]
        if results["cumulative_legendre_success"]
        else 0,
        "oppermann_success_rate": results["cumulative_oppermann_success"][-1]
        if results["cumulative_oppermann_success"]
        else 0,
    }
    with open(os.path.join(output_dir, "metadata.json"), "w", encoding="utf-8") as f:
        json.dump(metadata, f, indent=2, ensure_ascii=False)


def compute_statistics(results):
    n_tested = len(results["n"])
    if not n_tested:
        return None

    error = np.array(results["I1_error"], dtype=float)
    rel_error = np.array(results["I1_relative_error"], dtype=float)
    n_array = np.array(results["n"], dtype=float)

    stats = {
        "n_tested": n_tested,
        "n_range": (results["n"][0], results["n"][-1]),
        "exhaustive": scan_is_exhaustive(results["config"]),
        "legendre_success_rate": 100.0 * np.mean(results["legendre_holds"]),
        "oppermann_success_rate": 100.0 * np.mean(results["oppermann_holds"]),
        "legendre_failures": [n for n, ok in zip(results["n"], results["legendre_holds"]) if not ok],
        "oppermann_failures": [n for n, ok in zip(results["n"], results["oppermann_holds"]) if not ok],
        "error_mean": float(np.mean(error)),
        "error_median": float(np.median(error)),
        "error_max": float(np.max(error)),
        "rel_error_mean": float(np.nanmean(rel_error)),
        "I1_count_min": int(np.min(results["I1_real_count"])),
        "I2_count_min": int(np.min(results["I2_real_count"])),
        "I3_count_min": int(np.min(results["I3_real_count"])),
        "alpha": None,
    }

    mask = error > 0.01
    if np.sum(mask) > 5:
        log_n = np.log(n_array[mask])
        log_error = np.log(error[mask])
        stats["alpha"] = float(np.polyfit(log_n, log_error, 1)[0])

    return stats


def print_statistics(stats):
    scope = "EXAUSTIVA no range configurado" if stats["exhaustive"] else "AMOSTRAL"
    print("\n" + "=" * 72)
    print(f"RESULTADO {scope}")
    print("=" * 72)
    print(f"Pontos efetivamente testados: {stats['n_tested']}")
    print(f"n: {stats['n_range'][0]:,} a {stats['n_range'][1]:,}")
    print(f"Legendre nos pontos testados: {stats['legendre_success_rate']:.4f}%")
    print(f"Oppermann nos pontos testados: {stats['oppermann_success_rate']:.4f}%")
    print(f"Menor contagem em Legendre: {stats['I1_count_min']}")
    print(f"Menor contagem na metade inferior: {stats['I2_count_min']}")
    print(f"Menor contagem na metade superior: {stats['I3_count_min']}")
    print(f"Erro médio do preditor truncado: {stats['error_mean']:.3f} primos")
    print(f"Erro relativo médio do preditor: {stats['rel_error_mean']:.3f}%")
    if stats["alpha"] is not None:
        print(f"Expoente empírico do erro do preditor: alpha = {stats['alpha']:.4f}")
        print("Esse expoente descreve este experimento truncado; não é teste independente de RH.")


def create_plots(results, output_dir):
    os.makedirs(output_dir, exist_ok=True)
    n_array = np.array(results["n"])

    plt.figure(figsize=(10, 6))
    plt.plot(n_array, results["I1_real_count"], ".", label="contagem exata")
    plt.plot(n_array, results["I1_predicted"], ".", label="preditor truncado")
    plt.xlabel("n")
    plt.ylabel("primos em (n², (n+1)²)")
    plt.title("Legendre: contagem exata vs preditor pela fórmula explícita")
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, "overview_corrected.png"), dpi=150)
    plt.close()

    error = np.array(results["I1_error"])
    mask = error > 0.01
    if np.any(mask):
        plt.figure(figsize=(10, 6))
        plt.loglog(n_array[mask], error[mask], ".")
        plt.xlabel("n")
        plt.ylabel("erro absoluto do preditor")
        plt.title("Erro do preditor truncado (escala log-log)")
        plt.grid(True, alpha=0.3, which="both")
        plt.tight_layout()
        plt.savefig(os.path.join(output_dir, "analysis_corrected.png"), dpi=150)
        plt.close()


def main():
    if CONFIG["N_STEP"] < 1:
        raise ValueError("N_STEP deve ser >= 1")

    total_points = (CONFIG["N_END"] - CONFIG["N_START"]) // CONFIG["N_STEP"] + 1
    scope = "exaustivo no range" if scan_is_exhaustive(CONFIG) else "amostral"

    print("=" * 72)
    print("LEGENDRE + OPPERMANN | LABORATÓRIO NUMÉRICO")
    print("=" * 72)
    print(f"Modo: {scope}")
    print(f"Range configurado: {CONFIG['N_START']:,} a {CONFIG['N_END']:,}")
    print(f"Passo: {CONFIG['N_STEP']:,}")
    print(f"Pontos que serão realmente testados: {total_points:,}")
    print(f"Zeros usados no preditor truncado: {CONFIG['NUM_ZEROS']}")
    print("Aviso: o preditor usa rho = 1/2 + i*gamma; não é teste independente de RH.")

    gammas = load_or_compute_zeros(CONFIG["NUM_ZEROS"], CONFIG["CACHE_FILE"])
    results = create_results_structure()

    legendre_failures = 0
    oppermann_failures = 0
    total_start = time.time()

    values = range(CONFIG["N_START"], CONFIG["N_END"] + 1, CONFIG["N_STEP"])
    for i, n in enumerate(tqdm(values, desc="Processando n")):
        analysis = analyze_single_n(n, gammas)
        for key, value in analysis.items():
            results[key].append(value)

        legendre_failures += int(not analysis["legendre_holds"])
        oppermann_failures += int(not analysis["oppermann_holds"])
        current = i + 1
        results["cumulative_legendre_success"].append(100.0 * (current - legendre_failures) / current)
        results["cumulative_oppermann_success"].append(100.0 * (current - oppermann_failures) / current)

        if CONFIG["CHECKPOINT_INTERVAL"] and current % CONFIG["CHECKPOINT_INTERVAL"] == 0:
            path = save_checkpoint(results, CONFIG["OUTPUT_DIR"], current // CONFIG["CHECKPOINT_INTERVAL"])
            elapsed = time.time() - total_start
            print(f"Checkpoint em {path} | tempo decorrido: {elapsed/60:.1f} min")

    results["timestamp_end"] = datetime.now().isoformat()
    save_final_results(results, CONFIG["OUTPUT_DIR"])
    stats = compute_statistics(results)
    if stats:
        print_statistics(stats)
    create_plots(results, CONFIG["OUTPUT_DIR"])

    print("\nConclusão correta:")
    if stats and stats["exhaustive"]:
        print("Todos os n do range configurado foram verificados computacionalmente.")
    else:
        print("Apenas os n amostrados pela configuração foram verificados computacionalmente.")
    print("Isto é evidência numérica, não uma prova das conjecturas.")


if __name__ == "__main__":
    main()
