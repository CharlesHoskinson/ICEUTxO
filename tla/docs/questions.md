# Editorial Review: Starstream TLA+ Specification Documentation

**Generated**: 2026-01-26
**Mode**: full
**Personas**: 5 (default.md)
**Document**: tla/docs/ (9 files, ~3500 lines)
**References**: None

---

## Persona Reviews

### Junior Developer

**Background**: Recently completed bootcamp/CS degree, new to formal specification and blockchain concepts. Relies on documentation that doesn't assume prior knowledge.

**Lens**: "What assumed knowledge am I missing that would help me understand this?"

#### Questions

**Q1**: What exactly IS TLA+ and why should I learn it for this project?
- **Location**: README.md, "What this is" section (lines 3-4); SPECIFICATION_DEEP_DIVE.md, Section 2 "Why TLA+" (lines 57-66)
- **Why it matters**: The README mentions "TLA+ is a specification language" but doesn't explain what makes it different from a programming language. The deep dive explains why TLA+ was chosen over alternatives, but assumes I know what Coq, Isabelle, and Alloy are. As a junior dev, I need to understand: Is this a programming language? A tool? How is it different from writing tests?
- **Resolution**: Add a "TLA+ for Programmers" section early in README or SPECIFICATION_DEEP_DIVE explaining: (1) TLA+ is NOT code you run in production, (2) it's a mathematical specification that describes how a system SHOULD behave, (3) TLC is the tool that checks if your specification has bugs by exploring all possible states, (4) a simple analogy like "TLA+ is to your code what a blueprint is to a building."

**Q2**: What is a UTXO and why does it matter?
- **Location**: README.md lines 9-10, STATE_MACHINES.md lines 6-42, SPECIFICATION_DEEP_DIVE.md line 17
- **Why it matters**: "UTXO lifecycle" appears everywhere as if it's common knowledge. The glossary defines it as "State is carried by discrete 'outputs'" but this is circular. I don't understand: What is an "output"? How is this different from a bank account balance? Why does this model matter for blockchain?
- **Resolution**: Add a "Background: UTXO Model" section before diving into the specification. Include: (1) comparison with account-based model (like Ethereum), (2) concrete example: "Alice has $100 = Alice has a UTXO worth $100. When she spends $30, the old UTXO is destroyed and two new UTXOs are created: one worth $30 (to Bob) and one worth $70 (back to Alice)", (3) why this matters: UTXOs can't be "double spent" if the protocol is correct.

**Q3**: What are "stackless coroutines" and "algebraic effects"?
- **Location**: SPECIFICATION_DEEP_DIVE.md glossary (lines 18-21), multiple references throughout STATE_MACHINES.md
- **Why it matters**: These are advanced programming language concepts that I've never encountered in a bootcamp. The glossary defines them, but I don't understand WHY Starstream uses them or what problems they solve. Terms like "continuation", "PC (program counter)", and "suspended frame" are thrown around without explanation.
- **Resolution**: Add a "Why Coroutines and Effects?" section with: (1) simple problem statement: "Blockchain transactions often need to pause mid-execution to wait for external data (like price feeds)", (2) explain how traditional functions can't pause and resume, (3) show a concrete example of a UTXO that yields/suspends at a specific point, (4) link to external resources for readers who want deeper understanding of effects/coroutines.

**Q4**: How do I actually RUN this model checker?
- **Location**: README.md lines 69-102, USAGE.md entire document
- **Why it matters**: The README shows commands but assumes I know where to put `tla2tools.jar` and how Java classpaths work. USAGE.md is better but I'm confused: Do I need the Toolbox (GUI) OR the jar file? Can I use both? The spec directory path appears throughout but I'm on macOS.
- **Resolution**: Create a true "Getting Started Tutorial" that: (1) shows complete installation for Windows/Mac/Linux separately, (2) has a "verification checklist" (download jar → test Java works → clone repo → run simple command → expect this output), (3) includes a "first successful run" screenshot/example showing what "No errors found" looks like, (4) adds troubleshooting for the most common first-time issues.

**Q5**: What does "model checking configuration" mean in practice?
- **Location**: README.md lines 132-146 "Model bounds", SPECIFICATION_DEEP_DIVE.md lines 512-534 "MC_Starstream.tla and Starstream.cfg"
- **Why it matters**: I see constants like `MAX_UTXOS = 3` and `UTXO_ID_BOUND = 8` but don't understand the implications. What happens if I change these? Why are they set to these specific values? The documentation says "These bounds keep the state space manageable" but what IS a "state space"?
- **Resolution**: Add a "Understanding Model Bounds" section explaining: (1) "state space" = all possible combinations of system states, (2) concrete example: "With MAX_UTXOS=3, the checker will test scenarios with 0, 1, 2, and 3 UTXOs. With MAX_UTXOS=10, the combinations explode and checking takes days/weeks", (3) a simple table showing bound values → approximate runtime, (4) guidance on "start small (MAX_UTXOS=2) for quick tests, increase when you need thorough checking."

**Q6**: What do all these invariant names mean?
- **Location**: README.md lines 17-30 (invariants table), INVARIANTS.md entire catalog
- **Why it matters**: Names like `INV_LINEAR_NoDoubleSpend` and `INV_EFFECT_ContinuationMatch` use jargon I don't understand. "Linear consumption"? "Continuation"? The INVARIANTS.md catalog explains what each checks, but doesn't explain WHY these specific properties matter or what would go wrong if they didn't hold.
- **Resolution**: For each invariant category, add: (1) "What could go wrong" subsection with a concrete attack scenario, (2) example: For NoDoubleSpend, show "Without this invariant, Alice could spend the same $100 UTXO twice: once to Bob and once to Charlie, creating $200 from $100", (3) prioritize the list: "Critical (will lose money if violated)" vs "Nice-to-have (edge case protection)."

**Q7**: How do I read the state machine diagrams?
- **Location**: STATE_MACHINES.md lines 10-42 (UTXO lifecycle diagram)
- **Why it matters**: The ASCII art state machine diagram is helpful but I'm not sure how to interpret all the arrows. What do bidirectional arrows (`<-->`) mean? Can a UTXO skip states? The note "Consumption happens from Executing/Reserved during commit" (line 43) contradicts the diagram which shows consumption from multiple states.
- **Resolution**: Add a "Reading State Diagrams" guide explaining: (1) single arrow = one-way transition, double arrow = can go back and forth, (2) which transitions are automatic vs manual, (3) a "step-by-step transaction walkthrough" showing exactly which states a UTXO moves through in a complete transaction lifecycle, (4) reconcile the diagram with the note about where consumption actually happens.

**Q8**: What's the relationship between all these modules?
- **Location**: README.md lines 103-118 (file structure table), MODULES.md lines 5-14 (architecture layers), QUICK_REFERENCE.md lines 28-52 (module map)
- **Why it matters**: There are 12 TLA+ files and I don't know where to start reading. The dependency diagram is helpful but I don't understand what "Layer 1: Foundation" vs "Layer 3: Orchestration" means in practical terms. Should I read them in layer order? Or follow the dependency arrows?
- **Resolution**: Add a "Learning Path" section: (1) "Start here: StarstreamTypes.tla (10 minutes) - defines basic data structures", (2) "Next: StarstreamUTXO.tla (20 minutes) - shows how UTXOs work", (3) create a "beginner reading order" that covers 20% of the spec but teaches 80% of the concepts, (4) mark advanced modules with "⚠️ Advanced - return after understanding basics."

**Q9**: What does a counterexample trace actually show me?
- **Location**: USAGE.md lines 185-205 (Interpreting results), SPECIFICATION_DEEP_DIVE.md lines 872-895 (Interpreting Counterexample Traces)
- **Why it matters**: Both documents show example counterexample output but I don't know how to use it to find bugs. The trace shows "State 1, State 2, ... State 7" but I don't know: Does each state represent a line of TLA+ code? A time period? How do I map the state changes back to the actual specification to figure out what went wrong?
- **Resolution**: Add a "Debugging Your First Counterexample" tutorial with: (1) a complete worked example from a deliberately broken spec, (2) step-by-step process: "Look at the last state → identify which invariant failed → work backwards → find the action that caused it", (3) show how to add TLA+ `Print` statements to debug, (4) common patterns like "if you see a UTXO in both utxoSet and consumedSet, you have a double-spend bug."

**Q10**: What does "content-bound signature" mean?
- **Location**: README.md line 13 (authorization feature), SPECIFICATION_DEEP_DIVE.md lines 206-230 (StarstreamAuth.tla section), MODULES.md lines 106-136
- **Why it matters**: The spec checks `ValidSignature(sig, tx)` and mentions "signature binding to transaction contents" but I don't understand what this protects against. The deep dive says "This binding prevents attacks where a malicious party reuses a signature" but doesn't explain HOW or show an attack example.
- **Resolution**: Add an "Authorization Deep Dive" with: (1) attack scenario: "Without content binding, Mallory could copy Alice's signature from Transaction A (sending 10 ADA to Bob) and paste it onto Transaction B (sending 100 ADA to Mallory)", (2) show how `TxContentsHash` includes inputs, outputs, AND coordination, preventing this reuse, (3) note that the spec uses abstract signatures (not real crypto) and explain the limitation.

**Q11**: How do I add a simple new invariant to test my understanding?
- **Location**: EXTENDING.md lines 6-56 (Adding a new invariant section)
- **Why it matters**: The guide shows the mechanical steps (edit this file, add to config) but doesn't give a "baby's first invariant" example. I want to write something simple like "all UTXO IDs are positive" to verify I understand the process before tackling complex properties.
- **Resolution**: Add a "Tutorial: Your First Invariant" section with: (1) choose a trivial property to check: `INV_TUTORIAL_PositiveIds == \A u \in ledger.utxoSet : u.id > 0`, (2) walk through editing StarstreamInvariants.tla with before/after code blocks, (3) show the expected TLC output when it passes, (4) deliberately break it (`u.id >= 0` when 0 shouldn't be allowed) and show the counterexample, (5) explain how this process scales to real invariants.

**Q12**: What's the difference between "safety" and "liveness" properties?
- **Location**: INVARIANTS.md lines 641-684 (Liveness properties section), SPECIFICATION_DEEP_DIVE.md line 495-510 (Fairness conditions)
- **Why it matters**: The docs mention both but assume I know the difference. I see safety invariants check "this bad thing never happens" but liveness properties use unfamiliar operators like `[]` and `<>`. The note "require fairness conditions" doesn't explain what fairness means or why I'd need it.
- **Resolution**: Add a "Safety vs Liveness Primer" explaining: (1) Safety = "nothing bad happens" (example: no double-spend), Liveness = "something good eventually happens" (example: transactions don't hang forever), (2) why liveness is harder to check (requires exploring infinite behaviors), (3) fairness explained simply: "fairness means 'if an action CAN happen repeatedly, it eventually WILL happen' - prevents the checker from finding fake bugs where the system just never takes an enabled action", (4) when to use FairSpec vs StrongFairSpec.

---

### Domain Expert

**Background**: Senior engineer with 10+ years in formal methods and distributed systems. Skeptical of oversimplification.

**Lens**: "Is this technically accurate and complete enough for production use?"

#### Questions

**Q1**: The specification uses pessimistic locking but what about livelock scenarios where two transactions repeatedly release and re-acquire in the same order?
- **Location**: SPECIFICATION_DEEP_DIVE.md, Section 4 "Pessimistic Locking"
- **Why it matters**: Pessimistic locking can cause livelock with certain access patterns, which would manifest as starvation rather than invariant violation
- **Resolution**: Document whether livelock is prevented (e.g., by ordered acquisition) or whether it's considered acceptable (and why)

**Q2**: The model bounds `MAX_UTXOS = 3` and `MAX_PENDING_TXS = 2` seem very small. What bugs might only manifest at larger scales?
- **Location**: SPECIFICATION_DEEP_DIVE.md, Section 37; STRATEGY.md, lines 232-238
- **Why it matters**: Small-model verification provides confidence but can miss bugs that only appear with 4+ concurrent transactions or deeper state graphs
- **Resolution**: Document which classes of bugs are known to require larger bounds and whether any testing has been done at larger scales

**Q3**: The signature model assumes `ValidSignature(sig, tx)` checks structural properties but what prevents signature malleability attacks?
- **Location**: SPECIFICATION_DEEP_DIVE.md, Section 24; StarstreamAuth module
- **Why it matters**: In real crypto systems, signature malleability can allow transaction ID changes; the spec doesn't model this
- **Resolution**: Either add a malleability invariant or explicitly document why it's out of scope and how the implementation must handle it

**Q4**: The effect handling model allows effects to be handled "eventually" but what's the bound on effect stack depth?
- **Location**: SPECIFICATION_DEEP_DIVE.md, Section 10; INVARIANTS.md, INV_EFFECT_MustBeHandled
- **Why it matters**: Unbounded effect stacks could be used for DoS; the spec doesn't appear to bound stack depth
- **Resolution**: Document whether effect stack depth is bounded by the model or whether this is an implementation concern

**Q5**: Token conservation (INV_BALANCE_TxPreserved) checks per-transaction but what about total ledger conservation across all UTXOs?
- **Location**: INVARIANTS.md, INV_BALANCE_TxPreserved; SPECIFICATION_DEEP_DIVE.md, Section 19
- **Why it matters**: Per-tx conservation doesn't prevent bugs where genesis creates inconsistent totals or where the invariant itself is checked on stale data
- **Resolution**: Add a global ledger balance invariant that sums all UTXOs and verifies it matches expected total supply

**Q6**: The INV_LOCK_ValidReservation invariant says locked UTXOs must be in "Reserved" or "Executing" but the text mentions "Suspended_at_Effect" - which is correct?
- **Location**: INVARIANTS.md, lines 361-369; STATE_MACHINES.md, line 51
- **Why it matters**: There's an apparent inconsistency - if a UTXO raises an effect during execution, it becomes Suspended_at_Effect while still locked
- **Resolution**: Verify and correct the invariant definition to include Suspended_at_Effect state

**Q7**: The adversarial actions (InjectInvalidTx, RejectInvalidTx) are mentioned but not fully documented. What attack scenarios do they cover?
- **Location**: SPECIFICATION_DEEP_DIVE.md, Section 26.5; MODULES.md, StarstreamSpec actions
- **Why it matters**: Without knowing what adversarial behaviors are modeled, we can't assess what attacks are proven infeasible
- **Resolution**: Add a table of adversarial actions with the specific malformation they inject and which invariant should catch them

**Q8**: The spec mentions weak and strong fairness but doesn't explain which properties require which. Is SF_vars for HandleTxEffect necessary for all deployments?
- **Location**: SPECIFICATION_DEEP_DIVE.md, Section 15; USAGE.md, lines 312-333
- **Why it matters**: Strong fairness is a stronger assumption about the scheduler; using it when not needed weakens the verification
- **Resolution**: Document which liveness properties require weak vs strong fairness and whether safety checking needs any fairness

**Q9**: How does the specification handle transaction ordering? If two valid transactions T1 and T2 both try to spend UTXO X, which wins?
- **Location**: STRATEGY.md, "Adversarial ordering" section (line 146)
- **Why it matters**: The spec explores interleavings but doesn't model explicit ordering policies; real consensus will impose an order
- **Resolution**: Document whether the spec assumes any transaction can be ordered first (non-deterministic) and how that maps to consensus layer

**Q10**: The chunking strategy for large documents (>800 lines) mentions 50-line overlap but SPECIFICATION_DEEP_DIVE.md is 1080 lines. Was it chunked for this review?
- **Location**: SPECIFICATION_DEEP_DIVE.md (1080 lines)
- **Why it matters**: A 50-line overlap may not be enough for context in highly interconnected sections
- **Resolution**: Either increase overlap for technical documents or note chunking limitations in the output

---

### Security Auditor

**Background**: Security professional with blockchain and formal verification experience. Thinks like an attacker while advising like a defender.

**Lens**: "What attack surfaces are unmodeled or unexplained here?"

#### Questions

**Q1**: Effect stack overflow and resource exhaustion attacks are not bounded or modeled
- **Location**: StarstreamEffects.tla (lines 82-127), SPECIFICATION_DEEP_DIVE.md (Section 10), STRATEGY.md (lines 152-156)
- **Threat model**: An attacker can craft a coordination script that raises unlimited nested effects, causing unbounded stack growth. The `PushEffect` operation has no depth limit. In a real implementation, this enables DoS by exhausting memory or gas limits. The spec explicitly excludes "gas/execution costs and DoS modeling" (line 46 of DEEP_DIVE), leaving this entire attack class unanalyzed.
- **Resolution**: Add invariant `INV_EFFECT_StackDepthBounded` checking `Len(tx.coordination.effectStack) <= MAX_EFFECT_DEPTH`. Document that implementations MUST enforce depth limits before effect raising. Add security section explaining why gas metering is critical even though TLA+ doesn't model it.

**Q2**: Continuation ID collision and confused deputy attacks via effect handling
- **Location**: StarstreamEffects.tla (lines 28-44, 99-127), INV_EFFECT_ContinuationMatch (INVARIANTS.md lines 515-532)
- **Threat model**: `continuationId` is modeled as `ContinuationIdRange` (arbitrary integers), not cryptographically bound to frame content. An attacker could raise an effect with a forged continuationId matching a different UTXO's PC, causing the handler result to resume the wrong computation. The invariant only checks that pending effects match the *current* suspended UTXO's PC, but doesn't prevent ID prediction or collision attacks across transaction contexts.
- **Resolution**: Document that implementations must use cryptographic commitment (hash of frame + nonce) for continuationId, not sequential integers. Add security warning that weak continuation IDs enable "confused deputy" attacks where handlers resume unintended computations.

**Q3**: Time-of-check to time-of-use (TOCTOU) race in effect handling between suspension and resumption
- **Location**: StarstreamSpec.tla lines 128-155 (RaiseTxEffect, HandleTxEffect), INV_EFFECT_SourceSuspended (INVARIANTS.md lines 495-513)
- **Threat model**: Between `RaiseTxEffect` (which transitions UTXO to `Suspended_at_Effect`) and `HandleTxEffect` (which resumes), the UTXO's frame.pc is mutable. The invariant `INV_EFFECT_ContinuationMatch` checks equality at handling time, but doesn't prevent PC mutation between raise and handle. An attacker with ability to modify suspended UTXO state could change the PC, causing resumption at an arbitrary instruction pointer.
- **Resolution**: Add invariant `INV_EFFECT_PCImmutableWhileSuspended` ensuring suspended UTXOs' PC cannot change while they have pending effects. Document that frame integrity hash must be checked before resumption.

**Q4**: Missing authorization checks during coordination script execution phase
- **Location**: StarstreamSpec.tla lines 101-127 (StartProcessing, ProcessTxCall), STRATEGY.md lines 108-127
- **Threat model**: `StartProcessing` accepts arbitrary `calls` from `SampleCallSeqsForInputs` without verifying the transaction signer is authorized to invoke those specific method calls. The authorization invariants (`INV_AUTH_ValidSpend`, `INV_AUTH_OwnerOnly`) only check ownership of *inputs*, not permission to execute specific coordination logic. An attacker could submit a transaction spending their own UTXOs but with a malicious coordination script.
- **Resolution**: Add section to STRATEGY.md explaining "Coordination Script Authorization Model" - who defines coordination scripts, how they're validated, and what prevents malicious call sequences. Add invariant `INV_AUTH_CoordinationAuthorized`.

**Q5**: Signature replay across different ledger states or chain forks is not modeled
- **Location**: StarstreamAuth.tla lines 89-110 (TxContentsHash, ValidSignature), INV_AUTH_ValidSpend (INVARIANTS.md lines 120-140)
- **Threat model**: `TxContentsHash` commits to transaction contents (inputs, outputs, coordination) but does NOT include ledger state context (block height, chain ID, consumed set state). An attacker on a forked chain could replay a valid signature from chain A onto chain B where the same UTXO IDs exist but in different states.
- **Resolution**: Add to StarstreamAuth.tla a `LedgerContextDigest` including chain ID, block height, and ledger state root hash. Update `TxContentsHash` to include this context. Document that implementations MUST include chain-specific identifiers in signature digest.

**Q6**: NFT duplication through concurrent transaction finalization race
- **Location**: StarstreamSpec.tla lines 157-178 (FinalizeTx), INV_BALANCE_NFTUnique (INVARIANTS.md lines 205-221)
- **Threat model**: Two concurrent transactions (tx1, tx2) both in `Committing` phase could simultaneously call `FinalizeTx` with output specs containing the same NFT ID. The invariant checks uniqueness in `ledger.utxoSet` *after* commit, but doesn't prevent concurrent output creation. The spec uses pessimistic input locking but has NO locking on output creation.
- **Resolution**: Add invariant `INV_BALANCE_PendingOutputsNoNFTDuplication` checking that no two pending transactions' output specs contain the same NFT ID. Add guard to `FinalizeTx` requiring output NFT IDs are globally unique across *all* pending transactions.

**Q7**: Frame hash integrity is checked but not cryptographically enforced
- **Location**: StarstreamFrame.tla lines 186-203 (ComputeFrameHash, IsFrame), INV_FRAME_Integrity (INVARIANTS.md lines 537-553)
- **Threat model**: `ComputeFrameHash` is modeled as `<<pc, locals, methodId>>` (structured tuple), not a collision-resistant hash function. An attacker finding a PC/locals/methodId collision could forge frames that pass the integrity check. Implementations might use weak hash functions that enable collision attacks allowing frame forgery.
- **Resolution**: Add explicit security note: "SECURITY: Implementations MUST use collision-resistant cryptographic hash (SHA-256 minimum)." Add to STRATEGY.md under "Cryptographic primitives" explaining frame integrity depends on hash collision resistance.

**Q8**: Effect handling failure modes and partial execution rollback are underspecified
- **Location**: StarstreamEffects.tla lines 66-77 (HandlerResult, FailedHandlerResult), StarstreamSpec.tla lines 197-203 (StartRollback)
- **Threat model**: When `HandleTxEffect` provides a `FailedHandlerResult`, what happens to partially executed transaction state? The spec has `StartRollback` but doesn't model *partial* rollback scenarios where some effects were handled successfully before one failed. An attacker could exploit this to leave transactions in inconsistent states.
- **Resolution**: Add invariant `INV_EFFECT_AllOrNothingHandling` ensuring that if any effect fails, ALL effects in the transaction are marked as failed and the transaction moves to Rollback phase. Document that effect handling must be atomic.

**Q9**: Token bag arithmetic overflow and underflow attacks are not bounded
- **Location**: StarstreamTypes.tla lines 163-173 (TokenBagType, AddTokenBags), INV_ATK_NoNegativeTokens (INVARIANTS.md lines 597-611)
- **Threat model**: `AddTokenBags` performs unchecked addition. While `INV_ATK_NoNegativeTokens` prevents negative balances, there's no overflow protection. An attacker could craft a transaction with token quantities near maximum, causing integer overflow during addition, wrapping to small values, enabling token inflation.
- **Resolution**: Add constant `MAX_TOKEN_QUANTITY` representing implementation's integer width. Add invariant `INV_BALANCE_NoOverflow` checking all token operations stay below MAX_TOKEN_QUANTITY. Document that implementations require checked/saturating arithmetic.

**Q10**: Lock release timing and atomicity during rollback creates double-lock vulnerability
- **Location**: StarstreamLedger.tla (AbortTxInLedger operation), StarstreamSpec.tla lines 201-203 (FinishRollback), INV_LOCK_Exclusive (INVARIANTS.md lines 338-354)
- **Threat model**: During `FinishRollback`, input UTXOs must be unlocked and their `lockedBy` field cleared. If unlock is non-atomic, an attacker could observe a transaction mid-rollback where some inputs are unlocked but others aren't, potentially reserving already-unlocked UTXOs while the rolling-back transaction still references them.
- **Resolution**: Add invariant `INV_LOCK_AtomicRelease` ensuring that when a transaction transitions to Failed state, ALL its input locks are released atomically. Document that implementations must use transactional lock release.

**Q11**: UTXO ID allocation and consumed set exhaustion enables ID starvation DoS
- **Location**: StarstreamLedger.tla (CreateUTXOInLedger), StarstreamTypes.tla lines 144-152 (UTXO_ID_BOUND), INV_ATK_IdMonotonic (INVARIANTS.md lines 577-595)
- **Threat model**: UTXO IDs are allocated sequentially via `nextUtxoId` with bound `UTXO_ID_BOUND + 1`. The `consumedSet` grows unboundedly as UTXOs are spent. An attacker can spam transactions consuming UTXOs, filling `consumedSet` until `nextUtxoId` reaches the bound - permanent DoS.
- **Resolution**: Add section to STRATEGY.md explaining "ID Space Management" - how implementations should handle ID exhaustion (recycling, pruning, checkpoints). Document that consumed set must be pruned after sufficient confirmation depth.

**Q12**: Effect stack LIFO ordering assumption is not enforced by invariants
- **Location**: StarstreamEffects.tla lines 82-98 (stack operations), lines 135-141 (OrderedEffectStack predicate)
- **Threat model**: Effects are pushed/popped as a stack (LIFO), but `OrderedEffectStack` is defined as `TRUE` (no-op predicate). There's no invariant enforcing LIFO ordering is preserved during handling. An attacker exploiting a bug could handle effects out-of-order, causing inner effects to complete before outer effects, violating algebraic effect semantics.
- **Resolution**: Replace `OrderedEffectStack(stack) == TRUE` with actual ordering invariant. Add `INV_EFFECT_LIFOOrdering` checking effects are handled in reverse-push order. Document why LIFO ordering is security-critical.

#### Risk Summary

**Highest Risk (Immediate Implementation Impact)**:
- Q1: DoS via unbounded effect stack
- Q4: Missing coordination script authorization
- Q6: NFT duplication race in output finalization
- Q10: Non-atomic lock release during rollback

**Medium Risk (Documentation/Guidance Needed)**:
- Q2: Weak continuation ID binding
- Q5: Signature replay across chains
- Q7: Frame hash collision resistance requirements
- Q9: Token arithmetic overflow

**Spec Completeness (TLA+ Model Improvements)**:
- Q3: TOCTOU in effect PC mutation
- Q8: Partial effect rollback semantics
- Q11: UTXO ID exhaustion
- Q12: Effect stack ordering enforcement

---

### Core Developer

**Background**: Works on TLA+ specs and formal verification. Knows the gap between design docs and implementation.

**Lens**: "Does this actually match what we built and how it works?"

#### Questions

**Q1**: MODULES.md says `INV_LOCK_ValidReservation` allows states "Reserved, Executing" but INVARIANTS.md line 364 shows the same. However, STATE_MACHINES.md shows `Suspended_at_Effect` can also have `lockedBy = txId`. Which is the implemented behavior?
- **Location**: MODULES.md, INV_LOCK_ValidReservation; INVARIANTS.md, line 364; STATE_MACHINES.md, line 51
- **Why it matters**: Documentation inconsistency suggests either the invariant is wrong or the state machine diagram is incomplete
- **Resolution**: Verify against actual `StarstreamInvariants.tla` and update all docs to match

**Q2**: The `BeginExecuteUTXO` / `EndExecuteUTXO` operators are mentioned in STATE_MACHINES.md but MODULES.md doesn't list them as operators in StarstreamUTXO.
- **Location**: STATE_MACHINES.md, line 70; MODULES.md, StarstreamUTXO section
- **Why it matters**: Docs reference operators that aren't documented, making it unclear how to use them
- **Resolution**: Either document these operators in MODULES.md or clarify they're internal to StarstreamSpec

**Q3**: The transaction phases shown as 4 states in Section 13 header ("Multi-Phase Transaction Model") but the diagram shows 7 states. Which is authoritative?
- **Location**: SPECIFICATION_DEEP_DIVE.md, Section 13
- **Why it matters**: The section header says "4-phase" but lists Idle, Reserve, Executing, Committing, Rollback, Committed, Failed (7 states)
- **Resolution**: Correct the header to match actual phase count or clarify terminology (phases vs states)

**Q4**: `FcnRange` appears in INVARIANTS.md (line 481) but isn't documented anywhere. Is this a TLA+ built-in or a custom operator?
- **Location**: INVARIANTS.md, line 481 (INV_EFFECT_NoOrphans)
- **Why it matters**: Custom operators should be documented; built-ins should have references
- **Resolution**: Either document FcnRange in StarstreamTypes or add note that it's from TLA+ standard library

**Q5**: The adversarial action `InjectInvalidTx` is listed in StarstreamSpec actions (MODULES.md, line 415) but there's no corresponding operator documentation.
- **Location**: MODULES.md, StarstreamSpec actions table
- **Why it matters**: Adversarial testing actions should be documented so reviewers understand what's tested
- **Resolution**: Add operator signature and description for InjectInvalidTx and RejectInvalidTx

**Q6**: Sample execution trace uses `FrameAtYield(...)` constructor but MODULES.md lists `FrameAtYield(pc, vars, method)` - do the args match?
- **Location**: STATE_MACHINES.md, line 369; MODULES.md, StarstreamFrame constructors
- **Why it matters**: The trace shows abbreviated form which may confuse readers about actual usage
- **Resolution**: Show complete constructor call with all arguments in the trace

**Q7**: The config file reference shows `MC_Spec` as the specification but some docs reference `MC_FairSpec` and `MC_StrongFairSpec`. Are all three defined?
- **Location**: USAGE.md, lines 304-333; SPECIFICATION_DEEP_DIVE.md, Section 15
- **Why it matters**: Readers need to know which specs exist and which to use for different checking modes
- **Resolution**: List all defined specifications in MC_Starstream.tla documentation with their purposes

**Q8**: `HandleTopEffect(stack, result)` is described as "pop top effect after handling" but `HandleTxEffect` in MODULES.md doesn't show this operator being used.
- **Location**: MODULES.md, StarstreamEffects operations; STATE_MACHINES.md, line 251
- **Why it matters**: The effect handling flow isn't clear - does handling pop from the stack automatically?
- **Resolution**: Document the complete effect handling sequence showing which operators are called

**Q9**: The `SignTx` wrapper is mentioned (SPECIFICATION_DEEP_DIVE.md, line 387) but not in the transaction operators table in MODULES.md.
- **Location**: SPECIFICATION_DEEP_DIVE.md, line 385-387; MODULES.md, StarstreamTransaction section
- **Why it matters**: SignTx appears to be called after every state change but isn't documented as an operation
- **Resolution**: Add SignTx to the operations table with explanation of when it's called

**Q10**: INVARIANTS.md references `INV_BALANCE_PendingTxValid` but this doesn't appear in the combined `INV_Safety` invariant (line 694-715). Is it checked separately?
- **Location**: INVARIANTS.md, lines 188-200 and 694-715
- **Why it matters**: Unclear whether this invariant is actually checked during model checking
- **Resolution**: Either add to INV_Safety or document why it's checked separately

---

### Technical Writer

**Background**: Documentation professional focused on usability, findability, and task-orientation.

**Lens**: "Can users find what they need and accomplish their tasks?"

#### Questions

**Q1**: There's no clear "Getting Started" tutorial that walks through a complete example from clone to successful model check.
- **Location**: README.md, "Quick start" section
- **Why it matters**: Quick start shows commands but doesn't show expected output or verify success; users can't tell if they did it right
- **Resolution**: Add complete tutorial showing: clone, run command, see "No errors found", interpret what that means

**Q2**: The documentation has 9 files but no index or reading order recommendation for different user goals.
- **Location**: README.md, "Documentation" table
- **Why it matters**: Users with different goals (understand invariants vs run TLC vs extend spec) don't know where to start
- **Resolution**: Add personas/paths: "New to TLA+? Start with STRATEGY then USAGE. Want to add properties? See EXTENDING."

**Q3**: SPECIFICATION_DEEP_DIVE.md is 1080 lines with no internal table of contents or clear section navigation.
- **Location**: SPECIFICATION_DEEP_DIVE.md
- **Why it matters**: Finding specific information requires scrolling through 37 numbered sections
- **Resolution**: Add table of contents with anchor links at the top of the document

**Q4**: Cross-references between documents are inconsistent - some use `[DOCUMENT.md](DOCUMENT.md)` style, others just mention filenames.
- **Location**: Throughout all docs
- **Why it matters**: Users can't reliably click through to related content
- **Resolution**: Standardize all cross-references as clickable markdown links

**Q5**: The invariants in INVARIANTS.md are well-cataloged but there's no "which invariant should I use for X?" guide.
- **Location**: INVARIANTS.md
- **Why it matters**: Users verifying specific properties don't know which invariants apply to their concern
- **Resolution**: Add a "Choosing Invariants" section mapping security concerns to specific invariants

**Q6**: Code examples in SPECIFICATION_DEEP_DIVE.md don't have consistent formatting - some have syntax highlighting hints, others don't.
- **Location**: SPECIFICATION_DEEP_DIVE.md, various code blocks
- **Why it matters**: Inconsistent formatting reduces scannability and makes examples harder to read
- **Resolution**: Add ```tla language hint to all TLA+ code blocks

**Q7**: The module dependency diagram appears in both README.md and MODULES.md with slightly different formats. Which is authoritative?
- **Location**: README.md, lines 34-67; MODULES.md, lines 7-14
- **Why it matters**: Multiple versions of the same diagram create confusion about which is current
- **Resolution**: Keep one authoritative diagram in MODULES.md and reference it from README.md

**Q8**: USAGE.md "Common issues" section is helpful but doesn't link to relevant solutions elsewhere in the docs.
- **Location**: USAGE.md, lines 229-297
- **Why it matters**: Users encountering issues may need more context than provided in the troubleshooting section
- **Resolution**: Add "See also" links to relevant sections (e.g., state explosion -> STRATEGY.md bounds discussion)

**Q9**: The "What it proves" vs "What it doesn't prove" is split across README.md, SPECIFICATION_DEEP_DIVE.md Part V, and STRATEGY.md. Should be consolidated.
- **Location**: README.md lines 17-30; SPECIFICATION_DEEP_DIVE.md Part V; STRATEGY.md
- **Why it matters**: Users need to understand verification scope but information is scattered
- **Resolution**: Create single authoritative "Scope and Limitations" section with clear reference from other docs

**Q10**: Quick Reference (QUICK_REFERENCE.md) is only 54 lines and could include more commonly-needed information.
- **Location**: QUICK_REFERENCE.md
- **Why it matters**: Quick reference should be a go-to cheat sheet but is quite sparse
- **Resolution**: Add: common error meanings, invariant quick lookup table, state transition quick reference

---

## Cross-Cutting Themes

### Theme 1: Incomplete Beginner Onboarding

**Flagged by**: Junior Developer, Technical Writer

**Root cause**: Documentation assumes familiarity with TLA+, formal verification, and UTXO models. The glossary and primer are helpful but insufficient for true beginners.

**Related questions**:
- Q1-Q4 (Junior Developer): TLA+, UTXO, coroutine concepts undefined
- Q1-Q2 (Technical Writer): Missing tutorial and reading paths

**Recommended action**: Add "Prerequisites" section with links to TLA+ learning resources; expand glossary with diagrams; create "Getting Started" tutorial for complete beginners.

---

### Theme 2: Documentation Inconsistencies

**Flagged by**: Core Developer, Technical Writer, Domain Expert

**Root cause**: Multiple documents describe the same concepts with slight variations, creating confusion about which is authoritative.

**Related questions**:
- Q1 (Core Developer): INV_LOCK_ValidReservation states mismatch
- Q3 (Core Developer): 4-phase vs 7-state confusion
- Q7 (Technical Writer): Duplicate diagrams with different formats
- Q6 (Domain Expert): State descriptions inconsistent

**Recommended action**: Audit all documents for terminology and structural consistency; designate authoritative sources; add cross-reference validation.

---

### Theme 3: Security Scope Unclear

**Flagged by**: Security Auditor, Domain Expert

**Root cause**: The spec explicitly excludes many security concerns (crypto, network, MEV) but doesn't comprehensively catalog what attacks ARE modeled vs what must be handled at implementation level.

**Related questions**:
- Q1-Q2 (Security Auditor): Front-running, key compromise not modeled
- Q7 (Security Auditor): DoS/gas limits not modeled
- Q3 (Domain Expert): Signature malleability not addressed

**Recommended action**: Add "Security Model" section explicitly listing: attacks proven infeasible by spec, attacks out of scope (and why), implementation security requirements.

---

### Theme 4: Operator Documentation Gaps

**Flagged by**: Core Developer, Junior Developer

**Root cause**: Some operators are mentioned in examples or prose but not formally documented in MODULES.md.

**Related questions**:
- Q2, Q5, Q9 (Core Developer): Undocumented operators
- Q4 (Core Developer): FcnRange not explained
- Q8 (Junior Developer): AdaBag not defined in trace

**Recommended action**: Audit all operator references; add missing operators to MODULES.md; add operator index for searchability.

---

### Theme 5: Missing Decision Guidance

**Flagged by**: Junior Developer, Technical Writer, Domain Expert

**Root cause**: Docs explain what things are but not how to make decisions (which invariant? which bounds? how to debug?).

**Related questions**:
- Q10 (Junior Developer): How to debug counterexamples
- Q5 (Technical Writer): Which invariant for which concern
- Q2 (Domain Expert): Which bugs need larger bounds

**Recommended action**: Add decision trees and selection guides; add debugging workflow; add "choosing bounds" guidance.

---

## Prose Quality Assessment

| Dimension | Rating | Key Observations |
|-----------|--------|------------------|
| **Clarity** | Good | Technical writing is generally clear with good topic sentences. TLA+ primer is helpful. Some sections assume too much background. |
| **Accuracy** | Fair | Most content appears accurate but some inconsistencies between documents (state counts, operator lists). Needs verification against actual spec files. |
| **Completeness** | Fair | Core concepts well-covered but gaps in operator documentation, security scope, and beginner onboarding. Cross-references incomplete. |
| **Style** | Good | Minimal AI patterns detected. Writing is direct and technical. Good use of tables and diagrams. Sentence variety is adequate. |

### Strengths
- Comprehensive invariant documentation with clear definitions
- Good use of diagrams for state machines
- Helpful quick reference and cheat sheets
- Consistent markdown formatting within files
- Technical accuracy on core concepts

### Areas for Improvement
- Add beginner onboarding path and tutorial
- Consolidate scattered scope/limitations content
- Complete operator documentation in MODULES.md
- Add cross-document consistency checks
- Expand quick reference material

---

## Prioritized Checklist

### P0: Blocking (Must Fix)

- [ ] **INVARIANTS.md line 364**: INV_LOCK_ValidReservation should include "Suspended_at_Effect" per STATE_MACHINES.md line 51
- [ ] **SPECIFICATION_DEEP_DIVE.md Section 13**: Header says "4-phase" but lists 7 states - clarify terminology
- [ ] **MODULES.md StarstreamSpec**: Document InjectInvalidTx and RejectInvalidTx adversarial actions
- [ ] **SECURITY**: Add `INV_EFFECT_StackDepthBounded` to prevent DoS via unbounded effect stack growth
- [ ] **SECURITY**: Add `INV_BALANCE_PendingOutputsNoNFTDuplication` to prevent NFT duplication race during finalization
- [ ] **SECURITY**: Add `INV_LOCK_AtomicRelease` ensuring atomic lock release during rollback
- [ ] **STRATEGY.md**: Add "Coordination Script Authorization Model" section explaining script validation

### P1: High Priority (Should Fix)

- [ ] **README.md**: Add 2-3 sentence TLA+ introduction for newcomers
- [ ] **Throughout**: Define "PC" (program counter) on first use
- [ ] **MODULES.md**: Document BeginExecuteUTXO, EndExecuteUTXO operators or clarify they're internal
- [ ] **MODULES.md**: Add SignTx to transaction operations table
- [ ] **USAGE.md**: Add explicit note that "no errors" means "within configured bounds"
- [ ] **All docs**: Standardize cross-references as clickable markdown links
- [ ] **SPECIFICATION_DEEP_DIVE.md Section 0.6**: Expand UTXO glossary with diagram comparing to account model
- [ ] **New content**: Add "Security Model" section cataloging in-scope vs out-of-scope attacks
- [ ] **SECURITY**: Document cryptographic commitment requirement for continuationId (not sequential integers)
- [ ] **SECURITY**: Add chain context binding (chain ID, block height) to TxContentsHash to prevent replay
- [ ] **SECURITY**: Add frame hash collision resistance requirement note (SHA-256 minimum)
- [ ] **SECURITY**: Add `INV_BALANCE_NoOverflow` and document checked arithmetic requirement

### P2: Medium Priority (Next Revision)

- [ ] **SPECIFICATION_DEEP_DIVE.md**: Add table of contents with anchor links
- [ ] **README.md**: Add reading path recommendations for different user goals
- [ ] **New content**: Add complete "Getting Started" tutorial with expected output
- [ ] **INVARIANTS.md**: Add "Choosing Invariants" guide mapping concerns to invariants
- [ ] **USAGE.md**: Add debugging workflow with decision tree
- [ ] **SPECIFICATION_DEEP_DIVE.md Section 0.7**: Add Python/JavaScript equivalents for TLA+ syntax
- [ ] **MODULES.md**: Document FcnRange operator or note it's TLA+ standard library
- [ ] **STATE_MACHINES.md**: Show complete constructor calls in sample trace
- [ ] **QUICK_REFERENCE.md**: Expand with common errors, invariant lookup, state transitions
- [ ] **STRATEGY.md**: Document which liveness properties require weak vs strong fairness
- [ ] **New content**: Add adversarial action table showing what each tests
- [ ] **EXTENDING.md**: Add "Tutorial: Your First Invariant" with baby-steps example
- [ ] **New content**: Add "Safety vs Liveness Primer" explaining fairness, temporal operators

### P3: Low Priority (Nice to Have)

- [ ] **SPECIFICATION_DEEP_DIVE.md**: Add ```tla syntax hints to all code blocks
- [ ] **README.md/MODULES.md**: Consolidate module diagrams to single authoritative version
- [ ] **USAGE.md**: Add "See also" links in troubleshooting section
- [ ] **INVARIANTS.md**: Add INV_BALANCE_PendingTxValid to INV_Safety or document why separate
- [ ] **README.md line 76**: Specify exact filename to download from releases page
- [ ] **STATE_MACHINES.md line 251**: Clarify HandleTopEffect pops from stack automatically

---

## Summary

### Statistics

| Metric | Count |
|--------|-------|
| Total questions | 54 |
| Cross-cutting themes | 5 |
| P0 findings | 7 |
| P1 findings | 12 |
| P2 findings | 13 |
| P3 findings | 6 |

### Overall Assessment

The Starstream TLA+ specification documentation is comprehensive and technically solid for its intended expert audience. The core content - state machines, invariants, module structure - is well-documented with good use of diagrams and tables. However, the documentation has gaps for beginners (assumes TLA+ and UTXO familiarity), contains some internal inconsistencies that need verification against actual spec files, and lacks clear guidance on decision-making (which invariants to check, how to debug failures, what security properties are actually proven).

The three P0 issues are documentation inconsistencies that could mislead readers about actual spec behavior. The P1 issues primarily address onboarding gaps and missing documentation for operators that appear in examples.

### Recommended Next Steps

1. **Verify P0 inconsistencies** against actual TLA+ source files and correct documentation
2. **Add beginner onboarding** path with TLA+ prerequisites and expanded glossary
3. **Create "Security Model"** section explicitly scoping what the spec proves vs implementation concerns
4. **Audit operator references** and complete MODULES.md documentation
5. **Add decision guidance** for choosing invariants, bounds, and debugging approach
