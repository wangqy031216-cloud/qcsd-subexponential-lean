# Subexponential QCSD under Tensor Contraction (Lean 4 Formalization)

Complete, machine-checked Lean 4 (`v4.35.0` + Mathlib + Cslib) formalization of the main theorem `QCSD_main`: under the explicit exact tensor-contraction hypothesis `QCSD_TC10`, all three variants of binary two-block Quasi-Cyclic Syndrome Decoding (QCSD) over $R_n = \mathbb{F}_2[X]/(X^n - 1)$ — **Exact total weight** (`QCSD_Correct`), **Separated per-block weights** (`QCSD_CorrectSep`), and **Upper-bound weight** (`QCSD_CorrectLe`) — are solved deterministically in subexponential time $2^{O(n/\sqrt{\log n})}$ and polynomial space $\mathrm{poly}(n)$, returning both the exact solution count and a valid witness whenever a solution exists (or certifying unsatisfiability when the count is zero).

No assumptions are placed on $n \ge 2$ (e.g. primality or oddness), invertibility of $h$, randomness, or existence of a solution.

## Verification Status

- **Lean toolchain**: `leanprover/lean4:v4.35.0` (see `lean-toolchain` and `lake-manifest.json`)
- **Total proof size**: **~59,900 lines** across `QCSD/Defs.lean` and 15 proof modules
- **Zero `sorry` / `admit` / `axiom` / `native_decide` / `unsafe` / `set_option`** across the entire repository
- **Standard axioms only** (`Verify.lean`):
  ```text
  'QCSD_main' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

## Reproducing the Verification

```bash
lake build Master_QCSD_Main
lake env lean Verify.lean
```

`lake build Master_QCSD_Main` compiles the full dependency graph and checks `QCSD_main` in Lean's kernel. Running `lake env lean Verify.lean` prints the exact type of `QCSD_main` and confirms that it depends exclusively on Lean's standard axioms `[propext, Classical.choice, Quot.sound]`.

## Modeling Notes

- **Exact Tensor Contraction (`QCSD_TC10`)**: Formalized in `QCSD/Defs.lean` for loopless undirected multigraphs with parallel edges counted in vertex degrees (`QCSD_BoolTensorNetwork2`), exact non-negative integer contraction (`QCSD_contraction2`), and vertex predicates given explicitly as well-formed polynomial-size Boolean circuits (`QCSD_BoolCircuit`) uniformly encoded via `QCSD_encodeNet2`.
- **Instance Encoding**: `QCSD_encodeInstance` / `QCSD_encodeInstanceSep` encode $h, s \in R_n$ as $n$-bit vectors and $n, t$ (or $t_0, t_1$) in unary. Within the theorem domain ($t \le 2n$, $t_0, t_1 \le n$), the total input length is $\le 5n + 2 = \Theta(n)$, linearly equivalent to binary encoding.

## Module Map

| Layer | Module | Role |
|---|---|---|
| **Core Definitions** | `QCSD/Defs.lean` | Deterministic TM model (`QCSD_DetTM`, `QCSD_ComputesOnEncoded3`), QCSD instances & correctness (`Exact` / `Sep` / `Le`), Boolean circuits & tensor networks (`QCSD_BoolTensorNetwork2`, `QCSD_contraction2`), `QCSD_TC10` / `QCSD_TCClass2`, time/space bounds |
| **Algebra & 2-Layer DFT** | `Branch2_Algebra.lean`, `Glue_TwoLayerConv.lean` | Powers-of-3 parameters, quotient ring $\mathbb{F}_2[Y]/(Y^{2J}+Y^J+1)$, 2-layer radix-3 DFT orthogonality & inversion, carryless block convolution, cyclic fold (`TwoLayerConvSpec`) |
| **Tensor Network & Padding** | `Branch3_Network.lean`, `Branch5_PadAndSep.lean`, `Glue_NetworkAndConv.lean` | Composable `QCSD_BoolCircuit` library, unified 19-block / 14-edge QCSD tensor network (`N_exact`, `N_le`, `N_sep`), balanced binary carry-ripple weight tree & comparators, `QCSD_TCClass2` membership, linear edge bounds $2n \le S \le 420n$, contraction bijections, isolated-vertex padding functor `padNet` |
| **Bit-Stream & Register Machine** | `Branch7_EncodeNetSpec.lean`, `Branch6_EncoderMacros.lean`, `Branch6b_ParseAndEdges.lean`, `Branch8_CircuitEmitters.lean`, `Branch8b_TailCircuitsEmit.lean`, `Glue_MnetRMProg.lean` | Exact imperative bit-stream decomposition of `QCSD_encodeNet2 (padNet W N)`, 6-primitive register-machine model (`RMProg` / `RMExec`), input parsers, parameter computation, 14-block edge emitter, 19-block circuit emitters (`rmMnetExact`, `rmMnetLe`, `rmMnetSep`) |
| **Uniform TM Compiler** | `Branch4_TMCompiler.lean`, `Branch4_Phase1Dev.lean` | Compilation of arbitrary polynomial-time `RMProg`s to deterministic single-tape Turing machines (`QCSD_DetTM`) with exact `padNet W` output tape alignment and logarithmic register width (`compileRMProg_std_spec`, `compileRMProg_sep_spec`) |
| **Prefix Recovery & Asymptotics** | `Branch1_Recovery.lean` | Monadic TM combinators, $2n$-bit greedy prefix-pinning recovery algorithm calling `TC`, output flushing & decoding, subexponential time $2^{O(n/\sqrt{\log n})}$ and polynomial space bounds (`qcsd_tc_recover_{exact,sep,le}_v2`) |
| **Master Assembly** | `Master_QCSD_Main.lean`, `Verify.lean` | End-to-end proofs of `qcsd_exact_master`, `qcsd_sep_master`, `qcsd_le_master`, and `QCSD_main` |
