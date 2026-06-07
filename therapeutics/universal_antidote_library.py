"""
universal_antidote_library.py — Phage Display Universal Antidote System.

Simulates a phage display library designed to evolve high-affinity binders
against 8 target toxins simultaneously:

    1. Cyanide (CN-)
    2. Botulinum neurotoxin (BoNT)
    3. Tetanus toxin (TeNT)
    4. Ricin (RCA)
    5. Saxitoxin (STX)
    6. Alpha-amanitin (α-AMA)
    7. VX nerve agent
    8. Sarin (GB)

Uses multi-target simultaneous panning with negative selection against
cross-reactive clones. Copy-number weighted binding models avidity effects.

Key fixes from V1:
    - Sample increased 100×: 1,000 → 100,000 clones
    - Multi-target simultaneous panning (not sequential)
    - Negative selection against cross-reactive clones
    - Copy-number weighted binding computation
    
Structural type: ⟨𐑼; 𐑡; 𐑾; 𐑬; 𐑐; 𐑧; 𐑲; 𐑠; ⊙; 𐑒; 𐑳; 𐑷⟩
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Set
import math
import random
import json


# ═══════════════════════════════════════════════════════════════════════════
# §1  TOXIN & BINDER MODELS
# ═══════════════════════════════════════════════════════════════════════════

TOXINS = [
    "cyanide", "botulinum", "tetanus", "ricin",
    "saxitoxin", "alpha-amanitin", "VX", "sarin",
]

# Toxin properties (size, mechanism, LD50)
TOXIN_PROPERTIES = {
    "cyanide":         {"mass_da": 26.0, "class": "small_molecule",   "ld50_nm": 100_000},
    "botulinum":       {"mass_da": 150_000, "class": "protein",       "ld50_nm": 0.0001},
    "tetanus":         {"mass_da": 150_000, "class": "protein",       "ld50_nm": 0.001},
    "ricin":           {"mass_da": 66_000,  "class": "protein",       "ld50_nm": 0.1},
    "saxitoxin":       {"mass_da": 299.0,   "class": "small_molecule","ld50_nm": 0.5},
    "alpha-amanitin":  {"mass_da": 919.0,   "class": "small_molecule","ld50_nm": 0.3},
    "VX":              {"mass_da": 267.0,   "class": "organophosphate","ld50_nm": 0.01},
    "sarin":           {"mass_da": 140.0,   "class": "organophosphate","ld50_nm": 0.5},
}


@dataclass
class Binder:
    """
    A phage-displayed binder (ankyrin repeat / nanobody scaffold).
    
    Has affinity (Kd) for each toxin, cross-reactivity profile,
    and copy number for avidity modelling.
    """
    clone_id: int
    scaffold: str                       # "ankyrin", "nanobody", "DARPin", "affimer"
    affinities: Dict[str, float]        # Kd (M) for each toxin — lower is better
    copy_number: int = 1                # Surface copy number (avidity)
    enrichment_rounds: int = 0
    selected_for: Set[str] = field(default_factory=set)
    
    def affinity_to(self, toxin: str) -> float:
        """Kd for a specific toxin in molar."""
        return self.affinities.get(toxin, 1.0)  # 1.0 M = no binding
    
    @property
    def best_toxin(self) -> str:
        """Toxin with highest affinity (lowest Kd)."""
        return min(self.affinities, key=lambda t: self.affinities[t])
    
    @property
    def best_kd(self) -> float:
        """Best (lowest) Kd value."""
        return self.affinities[self.best_toxin]
    
    def affinity_score(self, toxin: str) -> float:
        """
        Binding score considering avidity (copy number).
        
        Avidity multiplies effective affinity: Kd_eff = Kd / copy_number
        Higher copy number → tighter effective binding.
        """
        kd = self.affinity_to(toxin)
        if kd <= 0:
            return float('inf')
        return 1.0 / kd * self.copy_number


def generate_random_binder(
    clone_id: int,
    scaffold: str = "ankyrin",
    n_toxins: int = 8
) -> Binder:
    """
    Generate a random binder with affinities to all toxins.
    
    Affinities follow a log-uniform distribution:
    - Most binders have Kd ~ 1e-6 to 1e-9 (μM to nM)
    - Rare binders reach 1e-10 to 1e-12 (pM to fM)
    """
    affinities = {}
    for toxin in TOXINS[:n_toxins]:
        # Log-uniform: random Kd between 1e-12 and 1e-3
        log_kd = random.uniform(-12, -3)
        kd = 10 ** log_kd
        affinities[toxin] = kd
    
    # Copy number: most 1, some up to 10
    copy_num = 1 if random.random() < 0.7 else random.randint(2, 10)
    
    return Binder(
        clone_id=clone_id,
        scaffold=scaffold,
        affinities=affinities,
        copy_number=copy_num,
    )
# ═══════════════════════════════════════════════════════════════════════════
# §2  PANNING — Multi-Target Simultaneous Selection
# ═══════════════════════════════════════════════════════════════════════════

class PhageLibrary:
    """
    Phage display library with multi-target simultaneous panning.
    
    Key improvements over V1:
    1. Sample size: 100,000 clones (was 1,000)
    2. Multi-target simultaneous: all 8 toxins panned in parallel
    3. Negative selection: remove cross-reactive binders before each round
    4. Copy-number weighted binding: realistic avidity modelling
    """
    
    def __init__(self, n_clones: int = 100_000, scaffold: str = "ankyrin"):
        self.n_clones = n_clones
        self.scaffold = scaffold
        self.binders: List[Binder] = []
        self.generation = 0
        self.enriched_clones: Dict[str, List[Binder]] = {t: [] for t in TOXINS}
        self.round_history: List[Dict] = []
        
        # Generate initial diverse library
        for i in range(n_clones):
            self.binders.append(
                generate_random_binder(i, scaffold)
            )
    
    def sample_clones(self, n: int) -> List[Binder]:
        """Sample n clones from library (without replacement)."""
        return random.sample(self.binders, min(n, len(self.binders)))
    
    def negative_selection(self, target_toxin: str, cutoff_kd: float = 1e-7) -> List[Binder]:
        """
        Remove binders that cross-react with non-target toxins.
        
        Any binder with affinity < cutoff_kd to a non-target toxin
        is removed before the positive selection round. This prevents
        enrichment of cross-reactive clones.
        
        Returns the remaining (filtered) binder list.
        """
        remaining = []
        for b in self.binders:
            cross_reacts = False
            for toxin, kd in b.affinities.items():
                if toxin != target_toxin and kd < cutoff_kd:
                    cross_reacts = True
                    break
            if not cross_reacts:
                remaining.append(b)
        return remaining
    
    def panning_round(self, target_toxin: str, wash_strictness: float = 1e-9) -> List[Binder]:
        """
        Perform one panning round for a specific toxin.
        
        Steps:
        1. Negative selection: remove cross-reactive binders
        2. Positive selection: bind to target toxin
        3. Wash: remove weak binders (Kd > wash_strictness)
        4. Elute: collect remaining binders
        5. Amplify and diversify (mutations)
        
        Returns enriched binders.
        """
        # Negative selection
        filtered = self.negative_selection(target_toxin, cutoff_kd=1e-7)
        
        # Positive selection — bind to target
        bound = []
        for b in filtered:
            kd = b.affinity_to(target_toxin)
            if kd < wash_strictness * b.copy_number:  # Avidity bonus
                b.enrichment_rounds += 1
                b.selected_for.add(target_toxin)
                bound.append(b)
        
        # Amplify and diversify (introduce point mutations)
        amplified = []
        for b in bound:
            # Keep parent
            amplified.append(b)
            
            # Generate mutants (2-3 per parent)
            for _ in range(random.randint(2, 3)):
                mutant = Binder(
                    clone_id=len(self.binders) + len(amplified),
                    scaffold=b.scaffold,
                    affinities=dict(b.affinities),
                    copy_number=max(1, b.copy_number + random.choice([-1, 0, 1])),
                )
                # Introduce affinity improvement (log-normal mutation)
                for toxin in mutant.affinities:
                    if random.random() < 0.3:  # 30% mutation rate
                        factor = 10 ** random.gauss(-0.5, 0.5)  # Mostly improve
                        mutant.affinities[toxin] *= factor
                
                mutant.enrichment_rounds = b.enrichment_rounds
                amplified.append(mutant)
        
        self.round_history.append({
            "round": self.generation + 1,
            "toxin": target_toxin,
            "input_count": len(filtered),
            "bound_count": len(bound),
            "output_count": len(amplified),
            "enrichment_ratio": len(bound) / max(1, len(filtered)),
        })
        
        return amplified
    
    def multi_target_panning(self, n_rounds: int = 8) -> Dict[str, List[Binder]]:
        """
        Perform multi-target simultaneous panning.
        
        In each round, ALL 8 toxins are panned simultaneously with
        separate negative selection for each. This prevents the
        sequential washout problem of V1.
        
        Returns enriched binders per toxin.
        """
        enriched = {t: [] for t in TOXINS}
        
        for rnd in range(n_rounds):
            self.generation = rnd + 1
            
            # Pan ALL toxins simultaneously in this round
            round_binders = []
            for toxin in TOXINS:
                pan_result = self.panning_round(toxin)
                enriched[toxin].extend(pan_result)
                round_binders.extend(pan_result)
            
            # Merge all enriched binders back into library
            self.binders = round_binders
        
        self.enriched_clones = enriched
        return enriched
    
    def compute_neutralization(self, toxin: str, concentration_nm: float = 1000.0) -> Dict:
        """
        Compute neutralization efficiency for a toxin at given concentration.
        
        Uses copy-number weighted binding model:
            Fraction bound = Σ (copy_i / Kd_i) / (concentration + Σ (copy_i / Kd_i))
        
        Each binder contributes proportionally to its avidity-adjusted affinity.
        """
        binders = self.enriched_clones.get(toxin, [])
        if not binders:
            return {"toxin": toxin, "neutralized": False, "fraction": 0.0, "n_binders": 0}
        
        # Copy-number weighted total affinity
        weighted_affinity = sum(
            b.copy_number / max(b.affinity_to(toxin), 1e-20)
            for b in binders
        )
        
        # Concentration in M
        conc_M = concentration_nm * 1e-9
        
        # Fraction of toxin bound (neutralized)
        fraction = weighted_affinity / (conc_M + weighted_affinity)
        
        return {
            "toxin": toxin,
            "neutralized": fraction > 0.99,  # >99% bound = neutralized
            "fraction": fraction,
            "n_binders": len(binders),
            "avg_kd": sum(b.affinity_to(toxin) for b in binders) / max(len(binders), 1),
        }
    
    def full_neutralization_profile(self) -> Dict[str, Dict]:
        """Compute neutralization for all 8 toxins at all relevant concentrations."""
        concentrations = [0.1, 1.0, 10.0, 100.0, 1000.0]  # nM
        profile = {}
        
        for toxin in TOXINS:
            toxin_results = {}
            for conc in concentrations:
                result = self.compute_neutralization(toxin, conc)
                toxin_results[f"{conc}_nM"] = result
            profile[toxin] = toxin_results
        
        return profile
# ═══════════════════════════════════════════════════════════════════════════
# §3  SIMULATION & VERIFICATION
# ═══════════════════════════════════════════════════════════════════════════

def run_antidote_simulation(
    n_clones: int = 100_000,
    n_rounds: int = 8,
    verbose: bool = True
) -> Dict:
    """
    Run full universal antidote library panning simulation.
    
    Args:
        n_clones: Initial library diversity (100,000 = 10^5).
        n_rounds: Number of panning rounds (8).
        verbose: Print progress.
    
    Returns:
        Dict with full results and neutralization profile.
    """
    # Initialise library
    library = PhageLibrary(n_clones=n_clones)
    
    if verbose:
        print(f"🧬 Phage Display Library Initialised")
        print(f"   Initial diversity: {library.n_clones:,} clones")
        print(f"   Scaffold: {library.scaffold}")
        print(f"   Targets: {len(TOXINS)} toxins")
        print()
        print("═══ PANNING ROUNDS ═══")
    
    # Multi-target simultaneous panning
    enriched = library.multi_target_panning(n_rounds=n_rounds)
    
    if verbose:
        for r in library.round_history:
            print(f"   Round {r['round']} ({r['toxin']}): "
                  f"{r['input_count']}→{r['bound_count']}→{r['output_count']} "
                  f"(enrichment: {r['enrichment_ratio']:.4f})")
    
    # Compute neutralization
    profile = library.full_neutralization_profile()
    
    if verbose:
        print()
        print("═══ NEUTRALIZATION PROFILE ═══")
        all_pass = True
        for toxin, results in profile.items():
            for conc_str, result in results.items():
                status = "✅" if result["neutralized"] else "❌"
                if not result["neutralized"]:
                    all_pass = False
                conc = conc_str.replace("_nM", " nM")
                print(f"   {status} {toxin} @ {conc}: "
                      f"{result['fraction']*100:.1f}% neutralized "
                      f"(n={result['n_binders']} binders, "
                      f"avg Kd={result['avg_kd']:.2e} M)")
        
        print(f"\n{'✅ ALL TOXINS NEUTRALIZED AT ALL CONCENTRATIONS' if all_pass else '❌ SOME FAILED'}")
    
    # Summary statistics
    total_binders = sum(len(bs) for bs in enriched.values())
    unique_binders = len(set(b.clone_id for bs in enriched.values() for b in bs))
    
    summary = {
        "initial_diversity": n_clones,
        "panning_rounds": n_rounds,
        "total_enriched_binders": total_binders,
        "unique_enriched_binders": unique_binders,
        "binders_per_toxin": {t: len(bs) for t, bs in enriched.items()},
        "avg_kd_per_toxin": {
            t: sum(b.affinity_to(t) for b in bs) / max(len(bs), 1)
            for t, bs in enriched.items()
        },
        "neutralization_profile": profile,
        "all_neutralized": all_pass,
    }
    
    return summary


def verify_neutralization(summary: Dict) -> Dict:
    """Verify all 8 toxins neutralized at all 5 concentrations."""
    checks = {}
    all_pass = True
    
    for toxin in TOXINS:
        for conc_label in ["0.1_nM", "1.0_nM", "10.0_nM", "100.0_nM", "1000.0_nM"]:
            result = summary["neutralization_profile"][toxin][conc_label]
            check_name = f"{toxin}_{conc_label}"
            checks[check_name] = result["neutralized"]
            if not result["neutralized"]:
                all_pass = False
    
    checks["all_pass"] = all_pass
    
    print("═══ ANTIDOTE VERIFICATION ═══")
    for check, passed in checks.items():
        if check == "all_pass":
            continue
        status = "✅" if passed else "❌"
        print(f"   {status} {check}")
    print(f"\n{'✅ ALL 40/40 CONCENTRATION-TOXIN PAIRS NEUTRALIZED' if all_pass else '❌ SOME FAILED'}")
    
    return checks


# ═══════════════════════════════════════════════════════════════════════════
# §4  MAIN — Run when executed directly
# ═══════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("═" * 60)
    print("  UNIVERSAL ANTIDOTE — Phage Display Library V2")
    print("═" * 60)
    print()
    
    # Run simulation
    summary = run_antidote_simulation(n_clones=100_000, n_rounds=8)
    
    print()
    print("═" * 60)
    print("  VERIFICATION SUITE")
    print("═" * 60)
    print()
    
    verify_neutralization(summary)
    
    print()
    print("═" * 60)
    print("  SUMMARY STATISTICS")
    print("═" * 60)
    print()
    print(f"  Total enriched binders: {summary['total_enriched_binders']:,}")
    print(f"  Unique enriched clones: {summary['unique_enriched_binders']:,}")
    for toxin, count in summary["binders_per_toxin"].items():
        avg_kd = summary["avg_kd_per_toxin"][toxin]
        print(f"  {toxin}: {count} binders, avg Kd = {avg_kd:.2e} M")
