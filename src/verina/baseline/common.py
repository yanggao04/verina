from verina.baseline.baseline import BaselineSolution
from verina.baseline.config import BaselineConfig
from verina.baseline.litellm_baseline import LiteLLMBaselineSolution
from verina.baseline.litellm_proof_refinement import LiteLLMProofRefinementSolution
from verina.baseline.proof_refinement import ProofRefinementSolution
from verina.benchmark.solution import Solution

__all__ = [
    "BaselineConfig",
    "BaselineSolution",
    "ProofRefinementSolution",
    "LiteLLMBaselineSolution",
    "LiteLLMBaselineSolution",
]


def get_baseline(config: BaselineConfig) -> Solution:
    """
    Get the baseline solution based on the config.
    """
    if config.name == "baseline":
        return BaselineSolution(config)
    elif config.name == "dsprover_baseline":
        return LiteLLMBaselineSolution(config)
    elif config.name == "proof_refinement":
        return ProofRefinementSolution(config)
    elif config.name == "dsprover_proof_refinement":
        return LiteLLMProofRefinementSolution(config)
    else:
        raise ValueError(f"Unknown baseline solution: {config.name}")
