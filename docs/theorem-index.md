# Theorem index

This page is written by `python scripts/find_theorem.py index --write`. Do not edit it by
hand. `python scripts/find_theorem.py index --check` fails when it is out of date.

It lists 604 theorems and 205 definitions of the Lean library.

## How to look something up

The page is long. To ask a question, use the tool, or grep this page.

```bash
python scripts/find_theorem.py search share token
python scripts/find_theorem.py show every_token_gets_a_share --proof --used-by
python scripts/find_theorem.py define COVERS_WITHIN
python scripts/find_theorem.py search --statement LipschitzWith --kind theorem --limit 5
python scripts/find_theorem.py file AttentionRate
python scripts/find_theorem.py chapter 36
```

The output is YAML, without the keys that are empty. Add `--json` for JSON with every key.
`search` ranks by name, doc comment, section heading and statement. `show` prints the
statement, where it is quoted and what uses it. An old name from
[RENAMES-theorems.txt](../lean/RENAMES-theorems.txt) finds the new one.
`python scripts/find_theorem.py --help` has more examples.

## What this does not do

- It does not know Mathlib. Only names declared under `lean/SquigglyLine` are here.
- Cross references are by name. A name used only through `open`, an alias, a macro or a
  structure projection may be missed. A name inside a comment is not a use.
  A name counts as used only if its file is the same file or one it imports.
- A book chapter is listed for a name when the chapter writes the whole name.
- A statement is cut at the first `:=` that no `let` used up; an unusual shape may be cut wrongly.

## Definitions

Every definition, abbreviation, structure and class, by name. Each line: the name, what
its doc comment says first, and the file (under `lean/SquigglyLine/`).

- `ADD_SKIP`: A residual layer: the input, plus what the branch makes of it. `Supporting/NetworkShape/Residual.lean`
- `Ambient`: The Euclidean space in which the line and the data live: the plane ... `Theorem/Defs.lean`
- `APPLY_ATTENTION_LAYER`: A layer of attention: every token is a query. `Supporting/NetworkShape/Attention.lean`
- `APPLY_BELLMAN_SWEEP`: One sweep of value updates: the new value of a state is its reward ... `Supporting/NetworkShape/Gain.lean`
- `APPLY_CONVOLUTION`: One convolution layer on a signal: each output is the kernel times ... `Supporting/NetworkShape/Convolution.lean`
- `APPLY_FAN`: One layer of the wind tunnel: rotate, then ReLU. `Networks/Polarizer.lean`
- `APPLY_GUIDANCE`: Classifier-free guidance with strength `guidance_strength` ... `Supporting/NewInputs/Mixing.lean`
- `APPLY_LEAKY_RELU`: A leaky ReLU: the input where it is positive, and a share `leak` of ... `Supporting/NetworkShape/Activations.lean`
- `APPLY_MESSAGE_PASSING`: One layer of message passing: each node becomes a weighted sum of the ... `Supporting/NewInputs/Mixing.lean`
- `APPLY_NARROW_LAYER`: A layer with a single neuron: `relu(weight * input + bias)`. `Networks/NarrowChain.lean`
- `APPLY_POST_NORM_BLOCK`: A post-norm block: the branch reads the stream, and the sum is ... `Supporting/NetworkShape/RmsNorm.lean`
- `APPLY_PRE_NORM_BLOCK`: A pre-norm block: the branch reads the normalised stream, and its ... `Supporting/NetworkShape/RmsNorm.lean`
- `APPLY_RELU_TO_PAIR`: ReLU on the plane: a negative coordinate becomes zero. `Networks/Polarizer.lean`
- `APPLY_SOFTMAX`: The share of class `chosen_class` when the scores are `scores`. `Supporting/Training/CrossEntropy.lean`
- `APPLY_STRAIGHT_THROUGH`: The straight-through trick at the point `anchor`: the hard value ... `Supporting/NetworkShape/HardChoices.lean`
- `APPLY_TENT`: One layer with two neurons: the tent `2 relu(x) - 4 relu(x - 1/2)`. `Networks/Depth.lean`
- `ARE_LABELS_ALMOST_SURELY_IN_BAND`: Almost every label lies in the band the sine sweeps: every label ... `Theorem/RandomPhase.lean`
- `ARE_MASKS_INDEPENDENT`: The masks of two different features are drawn independently: knowing ... `Supporting/Training/Dropout.lean`
- `ARE_MASKS_OF_VARIANCE`: Every mask has the same variance, `mask_variance`. `Supporting/Training/Dropout.lean`
- `ARE_MASKS_ONE_ON_AVERAGE`: Every mask is one on average, so dropout does not change the answer ... `Supporting/Training/Dropout.lean`
- `ATTEND`: One attention head answering one query: the values of the tokens ... `Supporting/NetworkShape/Attention.lean`
- `ATTEND_LINEARLY`: Attention without the softmax: the values weighted by the raw scores. `Supporting/NetworkShape/Attention.lean`
- `AVERAGE_OVER_MOVES`: A model averaged over a group of moves of the input. `Supporting/NewInputs/Mixing.lean`
- `BitString`: A string of bits. `Connections/ParityZigzag.lean`
- `BLEND`: The average of the predictions `predictions` with shares `shares`. `Supporting/NewInputs/Averaging.lean`
- `ClassArrows`: One arrow for each class. `Supporting/NetworkShape/NeuralCollapse.lean`
- `CLIP`: Clip a gradient to length at most `limit`, keeping its direction. `Supporting/Training/StepRules.lean`
- `ComplexLight`: Light with a phase: an across part and an up part, each a complex ... `Networks/TrainedPlate.lean`
- `COMPRESS`: Squeeze a model sideways by the factor `squeeze_factor`. `Theorem/Compression.lean`
- `CosineSinePair`: A point of the plane, written `!₂[cosine_part, sine_part]`, with the ... `Networks/FourierLift.lean`
- `Cost`: A cost charged to a model on one data point. `Theorem/Defs.lean`
- `COUNT_ONES`: How many of the bits are on. `Connections/ParityZigzag.lean`
- `COVERS_WITHIN`: Near every input, within distance `reach`, the model takes every ... `Theorem/Oscillation.lean`
- `DataDistribution`: The data as a distribution, when the inputs are real numbers. `Theorem/Vocabulary.lean`
- `DataDistributionOver`: The data as a distribution: a way to draw `(input, label)` pairs at ... `Theorem/Vocabulary.lean`
- `DataPoint`: A labelled example: an input and its real label. `Theorem/Defs.lean`
- `DENOISE_IDEALLY`: The ideal denoiser for the training examples `examples` at noise ... `Supporting/NewInputs/Averaging.lean`
- `DimpledInput`: An input of the dimpled model: a position on the manifold and a ... `Supporting/NewInputs/Dimple.lean`
- `DRAW_SINE_CURVE`: The curve drawn by one frequency and one phase. `Theorem/SquigglyLineTheorem.lean`
- `EMBED_DATA_POINT`: A data point, placed in the ambient Euclidean space. `Theorem/Defs.lean`
- `EntryVector`: A vector with one real entry for each of the `Entries`. `Supporting/NetworkShape/RmsNorm.lean`
- `EVALUATE_BUMP_NETWORK`: A radial basis network: bumps of one width at the centres, with the ... `Networks/RadialBasis.lean`
- `EVALUATE_DIMPLED_MODEL`: A function that is `profile` along the manifold and has slope `slope` ... `Supporting/NewInputs/Dimple.lean`
- `EVALUATE_FLAT_MODEL`: The flat function upstairs: the dot product of the weights with a ... `Networks/Lift.lean`
- `EVALUATE_LIFTED_MODEL`: A model linear in its weights: lift the input, then apply the flat ... `Networks/Lift.lean`
- `EVALUATE_ONE_HIDDEN_LAYER`: A network with one hidden layer. `Supporting/Training/Symmetry.lean`
- `EVALUATE_RAMP`: A ramp across the piece number `piece_index` of `piece_count` pieces ... `Supporting/NetworkShape/UniversalApproximation.lean`
- `EVALUATE_SHALLOW_NETWORK`: A network with one hidden layer of ReLU units, indexed by `units` ... `Supporting/NetworkShape/DepthSeparation.lean`
- `ExampleScores`: One score for each example: the outputs of a model on a list of ... `Supporting/Training/CrossEntropy.lean`
- `FeatureMap`: A lift: it turns an input into a feature vector. `Networks/Lift.lean`
- `FeatureTable`: The data, as a table: `feature_values example feature` is the value ... `Supporting/Training/Dropout.lean`
- `FLIP_LABEL_AT`: Change a labelling at the one input `input`. `Supporting/Training/Perceptron.lean`
- `GET_ANCHOR_SCORE`: A flat score for the anchor point `anchor`, read at the input `input`. `Supporting/Training/Perceptron.lean`
- `GET_AVERAGE`: The average of a random quantity. `Supporting/Training/Dropout.lean`
- `GET_AVERAGE_DISTANCE`: The nearest distance, averaged over the data and the random phase. `Theorem/SquigglyLineTheorem.lean`
- `GET_AVERAGE_LOSS`: The loss, averaged over the data and the random phase. `Theorem/SquigglyLineTheorem.lean`
- `GET_BIAS_FACTOR`: The part of the signal term that a floor takes away: none of it with ... `Supporting/NewInputs/BiasVariance.lean`
- `GET_BUMP`: The Gaussian bump of the given width, at an offset from its centre. `Networks/RadialBasis.lean`
- `GET_CODE_PENALTY`: The penalty a variational autoencoder puts on a code drawn from a ... `Supporting/NetworkShape/Mixtures.lean`
- `GET_CRITIC_LOSS`: The critic's loss at one input, where real data lands with weight ... `Supporting/Training/GanGame.lean`
- `GET_CROSS_ENTROPY`: The cross-entropy loss of the scores `scores` against the labels ... `Supporting/Training/CrossEntropy.lean`
- `GET_DESCRIPTION_LENGTH`: The cost of describing `weights` to someone who has the ... `Supporting/NetworkShape/CodeLength.lean`
- `GET_DISTANCE_FIELD`: The distance field of the line: at each point of space, the distance ... `Supporting/NetworkShape/SignedDistance.lean`
- `GET_FIT_DISTANCES`: The distances from the start to the weight vectors that fit the data. `Networks/LinearModel.lean`
- `GET_FLAT_BOUNDARY`: The flat boundary through the origin at right angles to `direction`. `Supporting/Training/Perceptron.lean`
- `GET_GRAPH`: The squiggly line: the graph of the model. `Theorem/Defs.lean`
- `GET_GRATING_STEP`: The step of the wave made by a plate whose axis turns half a turn ... `Networks/TravellingLight.lean`
- `GET_INPUT`: The input (the `x` part) of a data point. `Theorem/Defs.lean`
- `GET_LABEL`: The label (the `y` part) of a data point. `Theorem/Defs.lean`
- `GET_LASSO_COST`: The lasso cost of one weight: half the squared miss of the target ... `Supporting/Training/Regularisers.lean`
- `GET_LIFT_KERNEL`: The kernel of a lift: how much two inputs overlap upstairs. `Networks/Lift.lean`
- `GET_LIGHT_IN_WINDOW`: The brightness on the screen, added up over one window. `Networks/TravellingLight.lean`
- `GET_LINEAR_SCORE`: The score of a linear model with the given weights at the given input. `Supporting/NetworkShape/NetworkSlope.lean`
- `GET_LOG_LOSS`: The cross-entropy loss of one score `score` against a label `label` ... `Supporting/Training/CrossEntropy.lean`
- `GET_LOSS_ABOVE_FLOOR`: The loss above the floor for one split of the budget. `Supporting/Training/ComputeBudget.lean`
- `GET_NEAREST_DISTANCE`: The Euclidean distance from a data point to the nearest point of the ... `Theorem/Defs.lean`
- `GET_PARITY`: The parity of a string of bits: 0 if an even number are on, 1 if an ... `Connections/ParityZigzag.lean`
- `GET_PERCEPTRON_WEIGHTS`: The perceptron's weights after `mistake_count` mistakes. `Supporting/Training/Perceptron.lean`
- `GET_PLANE_DOT`: The dot product of two points of the plane. `Networks/Positions.lean`
- `GET_POSITION_OVERLAP`: The overlap of the sinusoidal signals of two positions, with one ... `Networks/Positions.lean`
- `GET_PRODUCT_ERROR`: The error of the two-weight model `first_weight * second_weight` on ... `Supporting/Training/Symmetry.lean`
- `GET_RESIDUAL`: What is left to fit: the labels minus the model's outputs. `Networks/LinearModel.lean`
- `GET_RESIDUAL_LOSS`: A loss that reads only the residual `label - model(input)`. `Theorem/Defs.lean`
- `GET_RIDGE_COST`: The weight-decay cost of one weight: the same, with the square of the ... `Supporting/Training/Regularisers.lean`
- `GET_RIDGE_FIT`: The fit that weight decay with penalty `decay_strength` rests at ... `Supporting/Training/WeightDecay.lean`
- `GET_ROOT_MEAN_SQUARE`: The root mean square of a vector: its length over the root of its ... `Supporting/NetworkShape/RmsNorm.lean`
- `GET_SIGNED_DISTANCE`: The signed distance from a data point to the line: positive above it ... `Supporting/NetworkShape/SignedDistance.lean`
- `GET_SINE_BAND`: The values a sine of this amplitude sweeps ... `Theorem/RandomPhase.lean`
- `GET_SPLIT_FIT`: The fit that gradient descent heads for when the residual is a signal ... `Supporting/NewInputs/BenignOverfitting.lean`
- `GET_TOTAL_LOG_LOSS`: The cross-entropy loss of the model `predict` over all examples. `Supporting/Training/CrossEntropy.lean`
- `GET_TRAVEL`: The distance in weight space from the start to the nearest fit. `Networks/LinearModel.lean`
- `GET_UNCOVERED_SET`: The part of the space that the tube of radius `radius` around the set ... `Theorem/Coverage.lean`
- `GET_VERTICAL_ERROR`: The vertical distance `|label - model(input)|` from a data point to ... `Theorem/Defs.lean`
- `GET_WEIGHTED_MEAN`: The mean of the points `points` with shares `shares`. `Supporting/NewInputs/Averaging.lean`
- `GOES_TO_ZERO_AS_INPUT_GROWS`: The quantity gets as close to zero as you like, once its input is ... `Theorem/Vocabulary.lean`
- `GradientPerStep`: One gradient for each step of training. `Supporting/Training/StepRules.lean`
- `HAS_HOMOGENEOUS_MARGINALS`: The output of the random model has the same distribution at every ... `Theorem/Compression.lean`
- `HAS_TIGHT_FEATURES`: The features are orthogonal on the data side, each with squared ... `Networks/ExchangeRate.lean`
- `HiddenVectors`: One row of hidden numbers for each item of a finite set. `Supporting/NetworkShape/Mixtures.lean`
- `HOLDS_FOR_EVERY_SINE`: The claim holds for every positive frequency and every phase. `Theorem/RandomPhase.lean`
- `InputPerExample`: One input for each training example. `Networks/Lift.lean`
- `InputReaders`: How each hidden unit reads the input: `read_input unit input` is the ... `Supporting/Training/Symmetry.lean`
- `INTERPOLATE_WITH_RELU`: The network made of the first `ramp_count` ramps, each scaled to ... `Supporting/NetworkShape/UniversalApproximation.lean`
- `IS_AFFINE_ON`: `model` is a straight line on the set `stretch`. `Supporting/NetworkShape/DepthSeparation.lean`
- `IS_BALANCED_SPLIT`: A split is balanced when the two terms of the loss are equal. `Supporting/Training/ComputeBudget.lean`
- `IS_IN_SINE_BAND`: The value lies in the band a sine of this amplitude sweeps. `Theorem/RandomPhase.lean`
- `IS_KERNEL_SUM`: The whole model `whole_predict` has the kept features `kept_predict` ... `Supporting/NewInputs/Pruning.lean`
- `IS_SAME_AT_EVERY_PLACE`: A gap is the same at every place: moving the light sideways before ... `Networks/TravellingLight.lean`
- `IS_SCALE_INVARIANT`: A loss that does not change when all the weights are multiplied by a ... `Supporting/Training/Symmetry.lean`
- `Kernel`: The weights of a convolution: one number for each offset under the ... `Supporting/NetworkShape/Convolution.lean`
- `Labelling`: A yes-or-no label for every input. `Supporting/Training/Perceptron.lean`
- `Layer`: One layer: it sends each state to the next state. `Networks/MarkovChains.lean`
- `LayerStack`: A stack of layers. `Networks/MarkovChains.lean`
- `LEARNING_CLAIM_HOLDS`: The learning claim: more parameters, smaller expected training loss ... `Theorem/Conjecture.lean`
- `LearningRatePerStep`: One step size for each step of training. `Supporting/Training/Optimisers.lean`
- `LEFT_CIRCULAR_LIGHT`: Circular light: the up part is the across part a quarter wave late. `Networks/TrainedPlate.lean`
- `LIFT_BY_BUMPS`: The lift of a radial basis network: the list of bump values at an ... `Networks/RadialBasis.lean`
- `LIFT_BY_FOURIER`: Wind the input round the unit circle at the given frequency. `Networks/FourierLift.lean`
- `LIFT_BY_FOURIER_SERIES`: The features of a Fourier series with frequencies `1` to ... `Supporting/Training/KernelSpectrum.lean`
- `LightAfterEachPlate`: The light after 0 plates, after 1 plate, after 2 plates, ... `Supporting/NetworkShape/SkipAndNorm.lean`
- `LightArrow`: An arrow in the plane: how far it reaches across, and how far up. `Networks/ThreePolarizers.lean`
- `LightOnLine`: Light along a line of points: one complex number at every point. `Networks/TravellingLight.lean`
- `LinearPredictor`: A model whose outputs on the data are linear in its weights: doubling ... `Networks/LinearModel.lean`
- `MAKE_DIMPLE`: The adversarial input for the label `label`: step straight off the ... `Supporting/NewInputs/Dimple.lean`
- `MAKE_LIGHT`: An arrow of length `amplitude` at angle `light_angle`: light of ... `Networks/ThreePolarizers.lean`
- `MAKE_PLATE_MATRIX`: The transition matrix of one plate. `Networks/MarkovChains.lean`
- `MAKE_RANDOM_PHASE_SINE`: The sine `amplitude * sin(frequency * input + phase)` with a ... `Theorem/RandomPhase.lean`
- `MAKE_RANDOM_PHASE_WAVE`: The wave `input ↦ profile(frequency * input + phase)` with a ... `Theorem/RandomPhase.lean`
- `MAKE_TWO_PRIME_WAVE`: The sum of the waves of two primes, as a function of the height. `Connections/PrimeWaves.lean`
- `MAKE_WAVE`: A wave across the line: the light at each point is `step` times the ... `Networks/TravellingLight.lean`
- `MARK_ACTION`: The label that says "action `taken_action` was taken": one for ... `Supporting/Training/PolicyGradient.lean`
- `Model`: A model: a function from inputs to real numbers. `Theorem/Defs.lean`
- `ModelFamily`: Random models indexed by a size: parameter count, depth, frequency. `Theorem/Conjecture.lean`
- `MomentumState`: The error now and the error one step ago, in one direction. `Supporting/Training/Optimisers.lean`
- `MOVE_ALONG`: The weights a fraction of the way from `start_weights` to ... `Networks/LinearModel.lean`
- `MoveChances`: The chance of each move: `move_chances state next_state` is the ... `Supporting/NetworkShape/Gain.lean`
- `NarrowLayer`: One layer with a single neuron: its weight and its bias. `Networks/NarrowChain.lean`
- `NarrowNetwork`: A network with one neuron per layer: the list of its layers. `Networks/NarrowChain.lean`
- `NEVER_TURNS`: A function that never turns: it only rises, or it only falls. `Networks/NarrowChain.lean`
- `NO_LIGHT`: No light at all: the arrow of length zero. `Networks/ThreePolarizers.lean`
- `NoiseTerm`: A number that depends on the random draw of the noise. `Supporting/NewInputs/BiasVariance.lean`
- `NORMALIZE_BY_RMS`: RMSNorm: a vector divided by its root mean square. `Supporting/NetworkShape/RmsNorm.lean`
- `NORMALIZE_SPECTRALLY`: Spectral normalisation: a layer divided by its own size. `Supporting/NetworkShape/Activations.lean`
- `NormBranch`: A branch of a block: it reads a vector and returns a vector of the ... `Supporting/NetworkShape/RmsNorm.lean`
- `NumberPerExample`: One number for each training example. `Networks/Lift.lean`
- `NumberPerState`: One number for each state: a table of rewards, or of guessed values. `Supporting/NetworkShape/Gain.lean`
- `PASS_COMPLEX_LIGHT_THROUGH_POLARIZER`: A polarizer acting on light with a phase: the shadow on the axis, as ... `Networks/TrainedPlate.lean`
- `PASS_THROUGH_NORMED_PLATES`: A stack of plates with axes `axes 1, axes 2, …`, an amplifier after ... `Supporting/NetworkShape/SkipAndNorm.lean`
- `PASS_THROUGH_PLATE`: A polarizer plate: the shadow of the light on the axis of the plate. `Supporting/NetworkShape/SkipAndNorm.lean`
- `PASS_THROUGH_PLATES`: A stack of `plate_count` plates. `Networks/ThreePolarizers.lean`
- `PASS_THROUGH_POLARIZER`: A polarizer with its axis at angle `axis_angle`: the shadow of the ... `Networks/ThreePolarizers.lean`
- `PASS_THROUGH_SKIP_PLATE`: A plate with a bypass: the light that went around is added to the ... `Supporting/NetworkShape/SkipAndNorm.lean`
- `PI`: The circle constant, 3.14159... `Style.lean`
- `PLACE_ON_EDGE`: A bird of a given length sitting on the edge of the quadrant ... `Networks/Polarizer.lean`
- `PLACE_ON_MANIFOLD`: A real data input: a position on the manifold, at height zero. `Supporting/NewInputs/Dimple.lean`
- `PlanePoint`: A point of the plane: how far across, and how far up. `Networks/Polarizer.lean`
- `PlateAxes`: A stack of plates, given by the axis of each: `axes 0`, `axes 1`, ... `Supporting/NetworkShape/SkipAndNorm.lean`
- `PlayerNumbers`: The two players' numbers: the maker's number and the critic's number. `Supporting/Training/GanGame.lean`
- `PREDICT_ON_EXAMPLES`: The outputs of a lifted model on a finite list of inputs, as a linear ... `Supporting/Training/KernelSpectrum.lean`
- `Profile`: One period of a wave: a function on the circle of circumference ... `Theorem/RandomPhase.lean`
- `RandomFunction`: A model `Inputs → ℝ` whose parameters are drawn at random. `Theorem/RandomFunction.lean`
- `RandomFunction.compress`: A random model, squeezed sideways by the factor `squeeze_factor`. `Theorem/Compression.lean`
- `RandomFunction.expected`: The expected cost at initialisation, on data drawn from ... `Theorem/RandomFunction.lean`
- `RandomFunction.marginal`: The one-point marginal: the distribution of the output at a single ... `Theorem/RandomFunction.lean`
- `RandomMask`: A random multiplier for each feature: `mask feature outcome` is what ... `Supporting/Training/Dropout.lean`
- `RandomSignal`: A signal whose size depends on a random outcome. `Supporting/NetworkShape/Gain.lean`
- `RandomVector`: A random vector: for each outcome, one number per coordinate. `Supporting/NewInputs/OnAverage.lean`
- `RealFunction`: A function from real numbers to real numbers. `Style.lean`
- `RENORMALIZE`: An amplifier that brings the light back to full strength. `Supporting/NetworkShape/SkipAndNorm.lean`
- `RESCALE`: The model `predict` with its parameters measured in units `scale` ... `Supporting/Training/Reparam.lean`
- `RIGHT_CIRCULAR_LIGHT`: Circular light of the opposite handedness. `Networks/TrainedPlate.lean`
- `ROTATE`: Rotation of the plane about the origin, anticlockwise, by an angle. `Networks/Polarizer.lean`
- `RUN_CELL`: The cell after `step_count` steps, with the gates and candidates of ... `Supporting/NetworkShape/Residual.lean`
- `RUN_LAYERS`: Run a stack of layers. `Networks/MarkovChains.lean`
- `RUN_NARROW_CHAIN`: A network with one neuron per layer. `Networks/NarrowChain.lean`
- `RUN_RESIDUAL_LAYERS`: A stack of residual layers: layer `layer_index` adds ... `Supporting/NetworkShape/Residual.lean`
- `RUN_SCHEDULE`: What is left of the error in a direction of strength `strength` after ... `Supporting/Training/Optimisers.lean`
- `ScoreFunction`: A score for each point `(first, second)` of the plane. `Supporting/Training/Perceptron.lean`
- `SEPARATES_XOR`: A score splits XOR when it is negative at `(0, 0)` and `(1, 1)` and ... `Supporting/Training/Perceptron.lean`
- `SHIFT_BY_ONE_POINT`: The same light, moved one point sideways. `Networks/TravellingLight.lean`
- `Shuffle`: A reordering of the hidden units: each unit is sent to another, and ... `Supporting/Training/Symmetry.lean`
- `Signal`: A signal: one number for each position. `Supporting/NetworkShape/Convolution.lean`
- `SinePhase`: The phase of a random-phase sine: a point on the circle. `Theorem/RandomPhase.lean`
- `SlopeLimit`: The steepest a model is allowed to be: a number that is not negative. `Theorem/Sandwich.lean`
- `SQUIGGLY_LINE_CONJECTURE_HOLDS`: The squiggly line conjecture: more parameters, smaller expected ... `Theorem/Conjecture.lean`
- `STARTS_CLOSER`: A bigger model has a strictly smaller expected cost at initialisation. `Theorem/Conjecture.lean`
- `TAKE_ADAM_STEP`: One coordinate of an Adam step with no memory of earlier steps: the ... `Supporting/Training/StepRules.lean`
- `TAKE_ADAM_STEP_WITH_L2`: Adam with the decay inside the loss: the pull `decay * weight` toward ... `Supporting/Training/AdamW.lean`
- `TAKE_ADAMW_STEP`: AdamW: Adam's step on the gradient alone, then the decay, not ... `Supporting/Training/AdamW.lean`
- `TAKE_DECAY_STEP`: One step of gradient descent with weight decay `decay_strength` ... `Supporting/Training/WeightDecay.lean`
- `TAKE_ERROR_STEP`: One training step, when the loss pushes the outputs `outputs` by ... `Supporting/Training/CrossEntropy.lean`
- `TAKE_GAME_STEP`: One simultaneous gradient step of the game with payoff `x * y`: the ... `Supporting/Training/GanGame.lean`
- `TAKE_GRADIENT_STEP`: One step of gradient descent on the squared error ... `Networks/Kernel.lean`
- `TAKE_MOMENTUM_STEP`: One step of gradient descent with momentum `momentum`, in a direction ... `Supporting/Training/Optimisers.lean`
- `TAKE_NOISING_STEP`: One noising step, on the pair (share of signal, share of noise) of ... `Supporting/NewInputs/Mixing.lean`
- `TAKE_STEP_ON_FIRST_WEIGHT`: The first weight after one gradient step on the loss `error² / 2`. `Supporting/Training/Symmetry.lean`
- `TAKE_STEP_ON_SECOND_WEIGHT`: The second weight after the same gradient step. `Supporting/Training/Symmetry.lean`
- `TokenScorer`: A rule that scores every token against every query, and may look at ... `Supporting/NetworkShape/Attention.lean`
- `TransitionMatrix`: A transition matrix on two states: entry `(row, column)` is the ... `Networks/MarkovChains.lean`
- `UPDATE_CELL`: One step of the memory cell of an LSTM: keep the share `forget_gate` ... `Supporting/NetworkShape/Residual.lean`
- `VarianceSplit`: The share of signal and the share of noise in the variance of a ... `Supporting/NewInputs/Mixing.lean`
- `Warp`: A rearrangement of the inputs, when the inputs are real numbers. `Theorem/Vocabulary.lean`
- `WarpOver`: A rearrangement of the inputs: where each input is moved to. `Theorem/Vocabulary.lean`
- `YesNoLabelling`: A yes or a no for each of the chosen inputs. `Supporting/NetworkShape/Capacity.lean`
- `YesNoNetwork`: A family of yes-or-no networks: a setting of the weights and an input ... `Supporting/NetworkShape/Capacity.lean`

## Theorems

By folder and file, in the order of the file. The numbers are the book chapters that
write the name.

### Theorem

#### [Compression.lean](../lean/SquigglyLine/Theorem/Compression.lean): The squiggly line theorem, for any function.

- `COVERS_WITHIN.squeezing_divides_the_reach`: Closer. (ch 7)
- `squeezing_multiplies_the_slope_limit`: Steeper. (ch 7)
- `squeezing_does_not_change_the_marginals`: No better. (ch 7)
- `squiggly_line_theorem_general`: The squiggly line theorem. (ch 7)

#### [Coverage.lean](../lean/SquigglyLine/Theorem/Coverage.lean): The tube identity.

- `point_is_uncovered_exactly_when_further_than_radius`: A point is uncovered at radius `radius` exactly when it is further than `radius` from the set.
- `mean_distance_equals_uncovered_mass_over_all_radii`: Tube identity.

#### [Defs.lean](../lean/SquigglyLine/Theorem/Defs.lean): Vocabulary of the squiggly line conjecture.

- `footpoint_is_on_the_line`: The point of the line directly above or below a data point.
- `data_point_is_on_the_line_exactly_when_label_is_output`: A data point is on the line exactly when its label is the model's output.
- `distance_between_data_points_is_by_pythagoras`: Pythagoras, for two data points in the ambient space.

#### [Marginal.lean](../lean/SquigglyLine/Theorem/Marginal.lean): A regression loss sees only one-point marginals.

- `expected_loss_at_a_point_is_an_average_over_the_marginal`: The expected loss on one data point is an integral against the one-point marginal. (ch 5)
- `equal_marginals_give_equal_expected_loss`: Marginal lemma. (ch 5)

#### [Oscillation.lean](../lean/SquigglyLine/Theorem/Oscillation.lean): What "squiggly" has to mean for the conjecture to hold.

- `nearest_distance_is_at_least_zero`: The distance to the nearest point of the line is never negative.
- `nearest_distance_is_at_most_reach`: Covering bound. (ch 4)
- `vertical_error_is_at_most_stretch_times_reach`: The slope tax. (ch 4)
- `covering_model_fits_any_target_after_a_small_warp`: Nearness can be used, by moving the input. (ch 4)
- `expected_nearest_distance_is_at_least_zero`: The expected distance to the nearest point is never negative.
- `expected_nearest_distance_is_at_most_reach`: Covering bound, in expectation.

#### [RandomPhase.lean](../lean/SquigglyLine/Theorem/RandomPhase.lean): Waves with a random phase.

- `marginal_of_random_phase_wave_is_profile_at_uniform_phase`: At every input, the wave's output is distributed as the profile at a uniform phase.
- `frequency_does_not_change_the_marginals_of_a_random_phase_wave`: Frequency is invisible in the marginals.
- `sine_on_the_circle_is_continuous`: The sine as a function on the circle of circumference `2 * PI`.
- `frequency_does_not_change_the_marginals_of_a_random_phase_sine`: The frequency of a random-phase sine does not change its one-point marginals. (ch 6)

#### [Sandwich.lean](../lean/SquigglyLine/Theorem/Sandwich.lean): The slope sandwich.

- `nearest_distance_is_at_most_vertical_distance`: The line is never further away than the vertical error. (ch 2)
- `cauchy_schwarz_in_the_plane`: Cauchy–Schwarz in the plane, in the form that the lower bound needs. (ch 3)
- `vertical_error_is_at_most_stretch_times_nearest_distance`: The vertical error is at most `√(1 + slope_limit²)` times the distance to the line. (ch 3)

#### [SineCloser.lean](../lean/SquigglyLine/Theorem/SineCloser.lean): The conjecture, settled for sines.

- `sine_covers_its_band_within_half_a_wave`: A real sine of frequency `frequency` takes every value in `[-|amplitude|, |amplitude|]` within ... (ch 6)
- `sine_passes_through_any_point_after_a_phase_shift`: Once the phase matches.
- `random_phase_sine_is_the_usual_sine`: With the phase written as a real number, the random-phase sine is the usual sine.
- `random_phase_sine_covers_its_band_within_half_a_wave`: Every draw of the random-phase sine covers its band within `PI / frequency`.
- `sine_slope_is_at_most_amplitude_times_frequency`: A sine of amplitude `amplitude` and frequency `frequency` has slope at most ... (ch 6)
- `nearest_distance_of_sine_is_between_two_bounds`: The distance for sines, pinned from both sides, at every data point and every phase.
- `sine_fits_any_target_in_its_band_after_a_small_warp`: A sine fits anything in its band, after a small warp. (ch 6, 48)
- `expected_nearest_distance_of_sine_is_at_most_half_a_wave`: The average distance for sines, with a rate.
- `expected_nearest_distance_of_sine_goes_to_zero`: The average distance for sines, in the limit. (ch 6)
- `closer_but_no_better`: Closer, but no better. (ch 6)

#### [SquigglyLineTheorem.lean](../lean/SquigglyLine/Theorem/SquigglyLineTheorem.lean): The squiggly line theorem, for sines.

- `squiggly_line_theorem`: The squiggly line theorem (for sines). (ch 2)

#### [Verdict.lean](../lean/SquigglyLine/Theorem/Verdict.lean): The verdict on the learning claim.

- `shared_marginals_never_start_closer`: A family with shared one-point marginals never starts closer in a regression loss.
- `higher_frequency_never_starts_closer`: Squiggliness does not lower the training loss.
- `learning_claim_fails_for_random_phase_waves`: The learning claim fails for random-phase waves whose frequency grows with size.
- `learning_claim_fails_for_random_phase_sines`: The experiment of `scripts/frequency_isolation.py`, as a theorem: for sines of any amplitude and ... (ch 6)

### Networks

#### [Bridge.lean](../lean/SquigglyLine/Networks/Bridge.lean): The bridge, part 1: a fold is a frequency doubling.

- `tent_keeps_the_unit_interval`: One tent layer keeps the unit interval inside the unit interval.
- `tent_layers_keep_the_unit_interval`: The wind tunnel keeps the unit interval inside the unit interval.
- `one_fold_doubles_the_angle`: One fold doubles the angle. (ch 8)
- `sine_squared_of_double_angle`: The double-angle formula for `sin²`.
- `folds_are_one_fourier_term`: `layer_count` folds are one Fourier term of frequency `2 ^ layer_count`. (ch 8)

#### [Depth.lean](../lean/SquigglyLine/Networks/Depth.lean): Depth multiplies the turns.

- `tent_rises_left_of_the_fold`: Left of the fold the tent rises: it doubles its input.
- `tent_falls_right_of_the_fold`: Right of the fold the tent falls: from 1 at the fold back to 0 at 1.
- `tent_layers_zigzag_on_the_grid`: Depth doubles the turns. (ch 49)

#### [DoubleDescent.lean](../lean/SquigglyLine/Networks/DoubleDescent.lean): Double descent, as the travel peak.

- `output_moves_at_most_length_times_distance`: The output on a feature vector moves by at most its length times the distance moved in parameter ...
- `fit_near_the_start_is_tame_everywhere`: A fit near the start is tame everywhere. (ch 10, 17)
- `travel_is_at_most_residual_over_root_of_kernel_floor`: The travel is large only where the kernel is weak.
- `kernel_is_symmetric`: The kernel is symmetric.
- `no_fit_along_a_direction_of_zero_strength`: Strength zero: out of reach. (ch 10)
- `travel_along_a_direction_equals_residual_over_root_of_strength`: Strength `strength`: the exact price. (ch 10)
- `weaker_direction_needs_at_least_as_much_travel`: The peak.
- `one_training_point_has_tight_features`: With one training point and feature vector `feature_vector`, the kernel is the squared length of ...
- `travel_for_one_point_equals_error_over_feature_length`: One training point.

#### [ExchangeRate.lean](../lean/SquigglyLine/Networks/ExchangeRate.lean): Parameter distance is loss, at an exchange rate.

- `HAS_TIGHT_FEATURES.pulling_back_scales_the_squared_length`: Pulling a vector back to weight space scales its squared length by `squared_length`.
- `HAS_TIGHT_FEATURES.outputs_change_at_most_root_of_squared_length_times_step`: A move of size `‖step‖` in parameter space changes the outputs by at most `√squared_length ‖step‖`.
- `HAS_TIGHT_FEATURES.travel_equals_residual_over_root_of_squared_length`: The exchange rate. (ch 9)
- `HAS_TIGHT_FEATURES.travel_equals_residual_for_orthonormal_features`: Parameter space is data space.

#### [FourierLift.lean](../lean/SquigglyLine/Networks/FourierLift.lean): The Fourier lift: winding the input round a circle.

- `flat_plane_over_the_circle_is_a_wave`: A flat plane over the circle is a wave.
- `fourier_kernel_is_cosine_of_the_gap`: The kernel sees only the gap. (ch 11)
- `fourier_kernel_does_not_change_under_a_shift`: Shifting both inputs by the same amount leaves the Fourier kernel as it was: the gap between them ...
- `squared_distance_of_fourier_lifts_is_a_chord`: The squared distance between two lifted inputs: the squared length of a chord of the unit circle.
- `fourier_lift_stretches_at_most_by_its_frequency`: The Fourier lift stretches by at most its frequency. (ch 11)
- `wave_slope_is_at_most_size_times_frequency`: A wave is no steeper than its size times its frequency.
- `shifting_data_and_question_changes_no_answer`: Shift the data and the question together and no answer changes.

#### [Initialisation.lean](../lean/SquigglyLine/Networks/Initialisation.lean): Standard initialisation: the squared loss at the start does not see the width.

- `one_outer_weight_as_product`: One outer weight, written as a product over all the units: the weight itself for the chosen unit ...
- `two_outer_weights_as_product`: Two outer weights multiplied, written as a product over all the units.
- `mean_of_one_outer_weight_equals_weight_mean`: The mean of one outer weight, when all are drawn independently from the same distribution, is the ...
- `mean_of_two_outer_weights_multiplied`: Two outer weights multiplied.
- `output_and_squared_output_have_means`: The output of the network and its square both have a finite mean.
- `squared_output_as_sum_over_pairs`: The square of the output is a sum over pairs of hidden units.
- `output_mean_is_zero_and_mean_square_has_no_width`: At the start, the mean output is zero and the mean squared output has no width in it. (ch 5)
- `expected_squared_error_at_start_has_no_width`: The expected squared error at the start has no width in it. (ch 5)
- `expected_squared_error_at_start_is_same_at_two_widths`: The same at two widths. (ch 5)

#### [Kernel.lean](../lean/SquigglyLine/Networks/Kernel.lean): The bridge, part 2: for training, a model is its kernel.

- `gradient_step_changes_residual_by_the_kernel`: Gradient descent sees only the kernel. (ch 10)
- `length_of_pulled_back_solution_depends_on_kernel_only`: The squared length of `A† K⁻¹ residual` is `⟪K⁻¹ residual, residual⟫`: it depends on the kernel ...
- `travel_depends_on_the_kernel_only`: Travel sees only the kernel.
- `same_kernel_gives_same_training_path`: Same kernel, same training path. (ch 10, 42)
- `same_kernel_gives_same_travel`: Same kernel, same travel. (ch 10, 42)

#### [Lift.lean](../lean/SquigglyLine/Networks/Lift.lean): Squiggly below, flat above: the kernel trick.

- `lifted_model_is_flat_model_after_the_lift`: The model downstairs is the flat function upstairs, applied after the lift.
- `flat_model_of_a_blend_is_the_blend`: Flat above.
- `point_is_on_the_line_exactly_when_its_lift_is_on_the_plane`: The squiggly line is the flat plane, seen through the lift. (ch 11)
- `squiggly_boundary_is_a_flat_boundary_upstairs`: A squiggly boundary is a flat one upstairs.
- `lifted_model_changes_at_most_weight_size_times_lift_distance`: The line changes by at most the size of the weights times how far the lift moves.
- `lifted_model_slope_is_at_most_tilt_times_stretch`: Slope is tilt times stretch. (ch 11)
- `vertical_error_of_lifted_model_is_at_most_stretch_times_nearest_distance`: The sandwich, in tilt and stretch.
- `kernel_trick`: The kernel trick. (ch 11)
- `lift_kernel_is_symmetric`: The kernel does not care which input comes first.
- `lift_kernel_over_all_pairs_is_a_squared_length`: A kernel summed over all pairs is a squared length.
- `lift_kernel_over_all_pairs_is_at_least_zero`: A kernel from a lift is never negative.
- `any_function_is_flat_in_some_lift`: Any function is flat in some lift. (ch 11)

#### [LinearModel.lean](../lean/SquigglyLine/Networks/LinearModel.lean): Where "a bigger model starts closer" is true: parameter space.

- `residual_along_the_path_is_a_share_of_the_start`: Every model walks the same loss curve. (ch 9)
- `residual_size_falls_in_a_straight_line`: The size of the residual falls in a straight line along the path to a fit.
- `fraction_of_the_path_is_that_fraction_of_the_distance`: A fraction of the way along the path is that fraction of the whole distance away from the start.
- `budget_of_travel_buys_its_share_of_the_loss`: Loss gap = distance × steepness. (ch 9)
- `more_weights_never_move_the_fit_away`: More weights never move the fit away. (ch 9)

#### [MarkovChains.lean](../lean/SquigglyLine/Networks/MarkovChains.lean): A chain of Markov chains.

- `running_two_stacks_is_running_one_after_the_other`: Running two stacks one after the other: first the early layers, then the late ones.
- `merged_stays_merged`: Merged stays merged. (ch 12, 34)
- `flock_never_spreads_over_more_places`: The flock never spreads over more places.
- `dead_stays_dead`: Dead stays dead. (ch 12)
- `blocked_photon_stays_blocked`: A blocked photon stays blocked.
- `bird_at_the_origin_stays_there`: A bird at the origin stays at the origin under any fan.
- `each_row_of_plate_matrix_sums_to_one`: Each row of the transition matrix is a probability distribution.
- `photon_chain_after_many_plates`: The photon's chain.
- `survival_probability_equals_squared_length`: The survival probability is the square of the surviving length: `(cos² angle) ^ plate_count` is ...
- `HAS_TIGHT_FEATURES.residual_after_many_gradient_steps`: The outer chain, solved. (ch 12)
- `HAS_TIGHT_FEATURES.one_gradient_step_fits`: One step fits.

#### [NarrowChain.lean](../lean/SquigglyLine/Networks/NarrowChain.lean): The tunnel that cannot turn.

- `narrow_layer_never_turns`: A single one-neuron layer never turns.
- `NEVER_TURNS.chain_never_turns`: Chaining two functions that never turn gives a function that never turns.
- `narrow_chain_never_turns`: A one-neuron-per-layer network never turns, whatever its depth and weights.
- `NEVER_TURNS.middle_output_is_between_the_outer_two`: What "never turns" means for three inputs in a row: the middle output lies between the outer two.

#### [Polarizer.lean](../lean/SquigglyLine/Networks/Polarizer.lean): ReLU as a polarizer with a wide opening.

- `relu_moves_to_the_nearest_number_that_is_not_negative`: On the number line, ReLU moves a number to the nearest number that is not negative: no other such ...
- `relu_is_a_projection_onto_the_quadrant`: ReLU is a projection. (ch 12)
- `fan_keeps_cosine_of_a_turn_up_to_a_quarter`: Malus's law.
- `fan_blocks_a_turn_beyond_a_quarter`: Crossed polarizers.
- `many_small_turns_keep_cosine_to_the_power`: Many small turns.
- `half_turn_in_many_steps_keeps_almost_everything`: The three-polarizer effect.

#### [Positions.lean](../lean/SquigglyLine/Networks/Positions.lean): Position embeddings.

- `position_overlap_equals_sum_of_cosines_of_the_gap`: The overlap of two positions is a sum of cosines of their gap.
- `position_overlap_does_not_change_under_a_shift`: So it depends only on the gap: moving both positions along by `shift` changes nothing.
- `position_overlap_is_at_most_frequency_count`: No two positions overlap more than a position does with itself.
- `position_overlap_with_itself_equals_frequency_count`: A position's overlap with itself is the number of frequencies.
- `dot_product_after_two_turns_depends_on_angle_gap`: Rotary positions.
- `rotary_score_depends_on_position_gap`: With angles `position * frequency`, the score depends on the two positions only through their gap.
- `turning_keeps_the_length`: Turning a vector does not change its length.
- `relative_bias_does_not_change_under_a_shift`: A relative position bias reads only the gap, so shifting the whole sequence leaves it as it was.
- `learned_table_ties_no_two_positions`: A learned table ties no two positions together.

#### [RadialBasis.lean](../lean/SquigglyLine/Networks/RadialBasis.lean): Radial basis functions: the width of a bump is its slope.

- `bump_is_greater_than_zero`: A bump is always above zero.
- `bump_is_at_most_one`: A bump is never higher than one.
- `bump_at_its_centre_equals_one`: At its centre a bump is one.
- `bump_is_the_same_on_both_sides`: A bump is the same on both sides of its centre.
- `bump_does_not_change_under_a_shift`: A bump sees only the distance between input and centre: shifting both changes nothing.
- `bump_is_the_unit_bump_squeezed`: A bump of width `width` is the unit bump, squeezed by `1 / width`. (ch 11)
- `unit_bump_slope_is_at_most_one`: The unit bump never climbs faster than one.
- `bump_slope_is_at_most_one_over_width`: A narrow bump is a steep one.
- `bump_network_slope_is_at_most_heights_over_width`: The network is no steeper than its heights over its width.
- `vertical_error_of_bump_network_is_at_most_stretch_times_nearest_distance`: Near needs narrow or tall.
- `bump_network_is_a_lifted_model`: A radial basis network is a flat model on the lift by bumps.
- `bump_away_from_its_centre_is_small`: Away from its centre by at least `gap`, a bump is at most `exp (-(gap / width)² / 2)`.
- `narrow_bumps_fit_anything`: Narrow bumps fit anything.
- `bumps_fit_when_narrower_than_the_gap`: How narrow is narrow enough. (ch 11)

#### [RandomFourier.lean](../lean/SquigglyLine/Networks/RandomFourier.lean): Random Fourier features: the Fourier lift, averaged, is the Gaussian bump.

- `average_cosine_under_a_bell_curve_is_a_bump`: The average cosine under a bell curve is a bump.
- `random_fourier_kernel_is_the_bump_kernel`: Random Fourier features give the radial basis kernel. (ch 11)

#### [TentCloser.lean](../lean/SquigglyLine/Networks/TentCloser.lean): A network for which the conjecture is true.

- `tent_layers_cover_within_one_over_two_to_the_layers`: Each fold halves the distance. (ch 8)
- `nearest_distance_of_tent_layers_is_at_most_one_over_two_to_the_layers`: More layers, closer. (ch 8)

#### [ThreePolarizers.lean](../lean/SquigglyLine/Networks/ThreePolarizers.lean): Three polarizers, and the photon's squiggly line.

- `malus_law`: Malus's law. (ch 12)
- `light_of_zero_strength_is_no_light`: Light of strength zero is no light, whatever its direction.
- `crossed_polarizer_blocks`: Crossed plates block. (ch 12)
- `light_after_many_plates`: The photon's path.
- `three_polarizers`: Three polarizers. (ch 12)
- `two_polarizers`: Without the plate in between, nothing reaches the vertical.
- `small_turns_lose_little`: A small turn loses little: `cos(turn_angle) ^ plate_count` is at least ...
- `quarter_turn_arrives`: More plates, closer. (ch 12)

#### [TrainedPlate.lean](../lean/SquigglyLine/Networks/TrainedPlate.lean): A plate whose angle is chosen at each point: what one point of it does.

- `plate_on_horizontal_light`: A plate on horizontal light.
- `plate_between_crossed_polarizers`: The trained three-polarizer experiment, at one point. (ch 12)
- `plate_on_circular_light`: A plate on circular light.

#### [TravellingLight.lean](../lean/SquigglyLine/Networks/TravellingLight.lean): Light that travels: what a gap can and cannot do.

- `wave_keeps_its_direction`: A gap keeps each wave. (ch 12)
- `beams_stay_beams`: Beams stay beams. (ch 12)
- `turning_plate_makes_three_waves`: A turning plate makes three waves. (ch 12)
- `turning_plate_makes_one_wave_of_circular_light`: With circular light a turning plate makes one wave. (ch 12)
- `three_waves_arrive_as_three_waves`: The three waves arrive as three waves. (ch 12)
- `brighter_lamp_scales_every_window`: A brighter lamp scales every window alike. (ch 12)
- `brighter_lamp_keeps_the_brightest_window`: The answer does not depend on the lamp. (ch 12)
- `one_plate_only_dims_a_glowing_point`: One plate only dims a glowing point. (ch 12)
- `one_plate_cannot_steer_a_glowing_point`: One plate cannot steer lamp light. (ch 12)

### Connections

#### [ParityZigzag.lean](../lean/SquigglyLine/Connections/ParityZigzag.lean): Parity is a zigzag: a first link to circuit lower bounds and P versus NP.

- `count_of_ones_is_at_most_bit_count`: No more bits are on than there are bits.
- `some_bit_string_has_each_count`: Every count from 0 to `bit_count` is the count of some string: turn on the first `ones_count` bits. (ch 49)
- `flipping_any_bit_flips_parity`: Flipping any one bit flips the parity. (ch 49)
- `deep_narrow_network_computes_parity`: A deep narrow network computes parity. (ch 49)
- `shallow_network_needs_one_unit_per_two_bits`: A shallow network needs one unit for every two bits. (ch 49)
- `shallow_network_on_right_side_of_half_needs_one_unit_per_two_bits`: The same, asking less of the network.
- `shallow_network_needs_one_unit_per_bit_less_one`: A shallow network needs one unit for every bit, less one. (ch 49)
- `half_of_all_functions_change_at_any_flip`: Exactly half of all functions change at any given flip. (ch 49)

#### [PrimeWaves.lean](../lean/SquigglyLine/Connections/PrimeWaves.lean): Waves of the primes: a first link to the Riemann zeta function.

- `ratio_of_prime_logs_is_irrational`: The frequencies of two different primes have an irrational ratio. (ch 48)
- `two_prime_clocks_reach_every_pair_of_phases`: Two prime clocks reach every pair of phases. (ch 48)
- `two_prime_wave_stays_inside_its_band`: The wave never leaves its band: it stays between minus and plus the sum of the two amplitudes. (ch 48)
- `two_prime_wave_takes_every_label_inside_its_band`: The sum of two prime waves takes every label inside its band. (ch 48)
- `irrational_steps_come_near_every_point_in_bounded_time`: Steps of an irrational size come near every point of the circle within a fixed number of steps. (ch 48)
- `two_prime_clocks_reach_every_pair_of_phases_within_a_fixed_distance`: Two prime clocks reach every pair of phases within a fixed distance of every height. (ch 48)
- `two_prime_wave_covers_a_narrower_band`: The sum of two prime waves covers a narrower band, with a finite reach. (ch 48)
- `two_prime_wave_fits_any_target_after_a_bounded_warp`: Any target in the narrower band is fitted exactly after a bounded warp. (ch 48)
- `two_prime_wave_slope_is_at_most_amplitudes_times_frequencies`: The wave of a prime is as steep as its frequency. (ch 48)
- `two_prime_wave_is_near_the_data_and_pays_the_slope_tax`: The squiggly line sandwich for the sum of two prime waves. (ch 48)
- `commensurate_wave_misses_part_of_its_band`: A wave whose two frequencies have a common period misses part of its band. (ch 48)

### Supporting/NetworkShape

#### [Activations.lean](../lean/SquigglyLine/Supporting/NetworkShape/Activations.lean): Activations and caps on slope.

- `sigmoid_slope_is_at_most_one_quarter`: The slope of a sigmoid, `sigmoid * (1 - sigmoid)`, is at most one quarter.
- `sigmoid_is_no_steeper_than_one_quarter`: A sigmoid is never steeper than one quarter. (ch 30)
- `sigmoid_layers_shrink_differences`: Sigmoid layers shrink differences. (ch 30)
- `leaky_relu_slope_is_at_most_one`: A leaky ReLU is no steeper than one. (ch 30)
- `leaky_relu_slope_is_at_least_its_leak`: A leaky ReLU keeps a slope of at least its leak. (ch 30)
- `leaky_relu_always_rises`: With a positive leak it is always rising: it merges no two inputs and is never dead. (ch 30)
- `pooling_never_steepens`: Pooling never steepens. (ch 30)
- `normalised_layer_size_is_at_most_one`: After spectral normalisation a layer has size at most one.
- `normalised_layer_size_equals_one`: For a layer that is not zero, the size is exactly one.
- `normalised_layer_slope_is_at_most_one`: A spectrally normalised layer has slope at most one. (ch 30)

#### [Attention.lean](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean): Attention: a weighted average, and one step of training.

- `attention_stays_inside_a_region_with_no_dents`: Attention averages. (ch 36)
- `attention_output_lies_among_the_values`: The output lies among the values. (ch 36, 37)
- `attention_keeps_merged_tokens_merged`: Merged stays merged.
- `equal_scores_give_equal_shares`: With equal scores every token gets the same share.
- `attention_with_equal_scores_is_the_plain_average`: With equal scores, attention is the plain average. (ch 37)
- `attention_alone_never_spreads_the_tokens`: Attention alone never spreads the tokens. (ch 36)
- `one_gradient_step_from_zero_weights`: One step of gradient descent from zero weights predicts, at a new input with features ... (ch 36)
- `one_gradient_step_is_a_linear_attention_head`: In-context learning. (ch 15, 36)
- `further_gradient_step_is_a_head_that_reads_the_errors`: A further layer reads the errors. (ch 36)

#### [AttentionRate.lean](../lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean): How fast attention merges the tokens.

- `two_weighted_averages_are_close`: Two weighted averages whose weights all sit above a common floor differ by at most the part they do ...
- `two_weighted_averages_differ_by_at_most_the_spread`: The same, for the size of the difference. (ch 36, 38)
- `every_token_gets_a_share`: Every token gets a share. (ch 36)
- `one_attention_layer_shrinks_the_spread`: One layer shrinks the spread. (ch 36)
- `depth_merges_the_tokens_at_a_geometric_rate`: Depth merges the tokens at a geometric rate. (ch 15, 36)

#### [Bottleneck.lean](../lean/SquigglyLine/Supporting/NetworkShape/Bottleneck.lean): The information bottleneck, by counting.

- `different_labels_must_stay_apart`: Different labels must stay apart. (ch 34)
- `labels_are_read_off_the_places`: The labels of a flock the network gets right are read off the places it occupies after the early ...
- `every_layer_keeps_at_least_as_many_places_as_labels`: The lower wall.
- `bottleneck`: The bottleneck. (ch 34)
- `full_compression_merges_exactly_equal_labels`: Full compression. (ch 34, 35)

#### [Capacity.lean](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean): Storage capacity: what a network can memorise.

- `fitting_everything_needs_one_parameter_per_number`: One parameter for each stored number. (ch 34)
- `too_few_weights_cannot_fit_something`: Too few weights: something cannot be fitted. (ch 34)
- `memorising_needs_two_to_the_inputs_settings`: Memorising `input_count` answers takes `2 ^ input_count` settings.
- `memorising_needs_one_bit_per_stored_bit`: One bit for each stored bit. (ch 34)

#### [CodeLength.lean](../lean/SquigglyLine/Supporting/NetworkShape/CodeLength.lean): Compression: folds, code length and travel.

- `digits_name_at_most_two_to_the_digits_things`: `digit_count` binary digits name at most `2 ^ digit_count` things. (ch 34)
- `fold_merges_an_input_with_its_mirror`: A fold merges an input with its mirror image.
- `fold_merges_nothing_else`: And with nothing else.
- `folds_throw_away_at_most_one_bit_each`: `fold_count` folds throw away at most `fold_count` bits. (ch 34)
- `gibbs`: No model beats the entropy. (ch 34)
- `no_code_beats_the_entropy`: No code beats the entropy. (ch 34)
- `gradient_descent_finds_the_cheapest_fit_to_describe`: Gradient descent finds the fit that is cheapest to describe. (ch 34)
- `bigger_model_fit_is_cheaper_to_describe`: A bigger model's fit is cheaper to describe. (ch 34)

#### [Convolution.lean](../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean): Convolution, stride and upsampling.

- `convolution_slope_is_at_most_summed_kernel`: A convolution is no steeper than its summed kernel. (ch 33)
- `convolution_reads_only_under_its_kernel`: A convolution is local. (ch 33)
- `convolution_stack_reads_only_its_window`: After `layer_count` layers an output sees only the inputs within `layer_count * kernel_width` of it. (ch 33, 41)
- `convolution_stack_reads_only_its_exact_window`: The window, one position tighter per layer. (ch 33)
- `stride_is_squeezing`: Stride is squeezing. (ch 33)
- `upsampling_is_squeezing_by_one_half`: Upsampling is squeezing by one half: a stretch. (ch 33)
- `squeezing_twice_multiplies_the_factors`: Squeezing twice multiplies the factors. (ch 33)
- `stride_after_upsampling_gives_the_signal_back`: A stride of two after an upsampling by two gives the signal back. (ch 33)
- `stride_doubles_the_slope`: Each stride doubles the slope of what the later layers see. (ch 33)

#### [DepthSeparation.lean](../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean): Depth separation: a shallow network pays one unit per turn.

- `IS_AFFINE_ON.const_mul`: A multiple of a straight line is a straight line.
- `IS_AFFINE_ON.not_zigzag`: A straight line cannot go up and come back down. (ch 32, 49)
- `sum_of_straight_lines_is_a_straight_line`: A sum of straight lines is a straight line.
- `line_crosses_zero_between_two_signs`: A line that is below zero at `input` and above zero at `middle` is zero somewhere strictly inside ...
- `relu_unit_is_straight_away_from_its_kink`: A ReLU unit is straight away from its kink. (ch 32)
- `every_up_and_down_holds_a_kink`: Every up-and-down holds a kink. (ch 32, 49)
- `one_unit_per_turn`: One unit per turn. (ch 32, 49)
- `depth_separation`: Depth separation. (ch 32)
- `evaluate_shallow_network_with_negated_gains`: Changing the sign of every output weight changes the sign of the output.
- `shallow_network_is_continuous`: A network with one hidden layer is continuous: a small change of the input makes a small change of ...
- `two_crossings_hold_a_kink_between_them`: Between two crossings of a level there is a kink.
- `one_unit_per_crossing_less_one`: One unit per crossing, less one. (ch 32, 49)
- `depth_separation_one_unit_per_inner_grid_point`: Depth separation, counted by crossings. (ch 32)

#### [Eikonal.lean](../lean/SquigglyLine/Supporting/NetworkShape/Eikonal.lean): The distance field falls at rate exactly one.

- `distance_falls_at_rate_one_toward_the_nearest_point`: Rate exactly one. (ch 29)
- `fall_in_distance_equals_length_walked`: The fall in distance equals the length walked. (ch 29)
- `every_point_has_a_nearest_point_with_rate_one`: In a space where closed balls are compact, every point has a nearest point of a closed set, and the ... (ch 29)
- `slope_of_distance_cannot_be_less_than_one`: The bound "slope at most one" cannot be improved. (ch 29)
- `distance_field_falls_at_rate_one_toward_the_line`: For the squiggly line. (ch 29)

#### [Gain.lean](../lean/SquigglyLine/Supporting/NetworkShape/Gain.lean): A gain per step: where it should be one, and where it should be below one.

- `fold_splits_the_squared_size_in_two`: A fold splits the squared size in two. (ch 30)
- `fold_keeps_half_of_a_symmetric_signal`: A fold keeps half. (ch 30)
- `he_gain`: The factor two of He initialisation. (ch 30)
- `sweep_slope_is_at_most_the_discount`: A sweep has slope at most the discount. (ch 30)
- `repeated_sweeps_pull_every_guess_to_one_answer`: Repeated sweeps pull every guess to one answer. (ch 30)

#### [HardChoices.lean](../lean/SquigglyLine/Supporting/NetworkShape/HardChoices.lean): Hard choices: the straight-through trick, a cold softmax, and Hopfield recall.

- `hard_step_sends_no_gradient_back`: A hard step sends no gradient back. (ch 39)
- `straight_through_forward_is_the_hard_step`: Forward, it is the hard step. (ch 39)
- `straight_through_backward_has_the_stand_in_slope`: Backward, it has the slope of the stand-in. (ch 39)
- `cold_softmax_picks_the_top_score`: A cold softmax picks the top score. (ch 15, 39)
- `hopfield_recall_equals_ideal_denoiser`: Hopfield recall is the ideal denoiser. (ch 39)
- `hopfield_recall_equals_ideal_denoiser_for_any_state`: Hopfield recall is the ideal denoiser, for a state of any length. (ch 39)

#### [KolmogorovArnold.lean](../lean/SquigglyLine/Supporting/NetworkShape/KolmogorovArnold.lean): Kolmogorov–Arnold networks: a learnable curve on an edge is a few folds.

- `edge_curve_is_a_few_folds`: An edge curve is a few folds. (ch 32)
- `folds_needed_go_as_slope_over_error`: Folds needed go as total slope over error.

#### [Mixtures.lean](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean): Gates, codes and a narrow last layer.

- `gate_adds_slope_only_through_the_spread`: A gate adds slope only through the spread of the experts. (ch 34)
- `code_penalty_charges_for_travel`: The penalty charges for travel.
- `code_penalty_is_at_least_zero`: The penalty is never negative.
- `code_penalty_is_zero_exactly_for_the_code_that_ignores_its_input`: It is zero only for the code that ignores its input: centre zero and width one, the same for every ...
- `softmax_bottleneck`: The softmax bottleneck. (ch 34)
- `some_score_table_cannot_be_matched`: So with more contexts than hidden numbers, some table cannot be made: for one, the table that ...

#### [ModeConnectivity.lean](../lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean): Mode connectivity: when two fits are joined by a straight line.

- `residual_on_the_line_between_two_settings`: On the straight line between two settings of the weights, the error is the matching blend of the ... (ch 35)
- `line_between_two_fits_is_all_fits`: The line between two fits is all fits. (ch 35)
- `no_barrier`: There is never a hill. (ch 35)
- `two_layer_hill_exactly`: The hill, exactly. (ch 35)
- `mirror_image_is_the_same_function`: A mirror image is the same function. (ch 35)
- `halfway_to_the_mirror_image_everything_is_lost`: Halfway to the mirror image, everything is lost. (ch 35, 37)

#### [NetworkSlope.lean](../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean): How steep a network can be, and what that slope costs.

- `network_slope_is_at_most_product_of_layer_slopes`: A network is no steeper than the product of its layers. (ch 28)
- `relu_slope_is_at_most_one`: A ReLU has slope at most one. (ch 28)
- `layer_slope_is_at_most_weight_size`: A layer "weights, then an activation of slope at most one" is no steeper than the size of the ... (ch 28)
- `vertical_error_of_network_is_at_most_stretch_times_nearest_distance`: The sandwich for a network. (ch 28)
- `backpropagation_runs_the_layers_in_reverse`: Backpropagation runs the layers in reverse. (ch 28)
- `gradient_coming_back_is_at_most_the_same_product`: The gradient coming back is bounded by the same product of sizes as the signal going forward. (ch 28)
- `flipping_a_classifier_needs_a_move_of_score_over_slope`: Flipping a classifier takes a move of at least score over slope. (ch 26, 28)
- `worst_small_nudge_moves_the_score_by_size_times_summed_weights`: The worst small nudge. (ch 28)
- `no_nudge_moves_the_score_by_more`: No nudge of at most `size_limit` per input moves the score by more. (ch 28)
- `larger_score_has_larger_share`: A larger score has a larger share. (ch 28)
- `temperature_never_changes_the_ranking`: Temperature changes confidence, never the ranking. (ch 28)
- `critic_of_slope_one_reports_at_most_the_distance`: A critic of slope one cannot report more than the distance. (ch 27, 28)

#### [NeuralCollapse.lean](../lean/SquigglyLine/Supporting/NetworkShape/NeuralCollapse.lean): Neural collapse: why the classes end up on a simplex.

- `squared_length_of_a_sum_is_the_sum_of_overlaps`: The squared length of a sum is the sum of all the overlaps. (ch 35)
- `all_classes_but_one`: All the classes but one: there are `class_count - 1` of them.
- `overlaps_of_one_arrow_with_all_arrows`: One arrow's overlaps with all the arrows: its own length, then the others.
- `sum_of_arrows_is_short_when_overlaps_are_small`: If every pair of arrows has overlap at most `overlap_limit`, their sum is short.
- `simplex_is_as_far_apart_as_arrows_get`: The simplex is as far apart as arrows can get. (ch 35)
- `squared_length_of_sum_of_evenly_spread_arrows`: If every pair of arrows has overlap exactly `overlap`, the squared length of their sum is ...
- `farthest_apart_arrangement_is_the_centred_one`: The farthest-apart arrangement is the centred one. (ch 35)

#### [Residual.lean](../lean/SquigglyLine/Supporting/NetworkShape/Residual.lean): Residual layers: what a skip does to squiggle.

- `residual_layer_slope_is_at_most_one_plus_branch`: A residual layer is no steeper than one plus its branch. (ch 31)
- `skip_keeps_points_apart`: A skip keeps points apart. (ch 31)
- `residual_layer_merges_no_two_inputs`: With a branch of slope below one, a residual layer never merges two inputs. (ch 31)
- `residual_layer_always_rises`: With one input and a branch of slope below one, a residual layer is always rising.
- `residual_layer_never_turns`: A turn has to be bought in the branch. (ch 31)
- `compound_growth_is_at_most_the_exponential`: `(1 + exponent / layer_count) ^ layer_count` never passes `e ^ exponent`. (ch 31)
- `residual_stack_slope_is_at_most_compound_growth`: `layer_count` residual layers with branches of slope at most `slope_limit` have slope at most ...
- `depth_does_not_blow_up_the_slope`: Depth does not blow up the slope. (ch 31)
- `cell_slope_is_the_forget_gate`: The slope of the cell is the forget gate.
- `gate_never_moves_two_memories_apart`: A gate between zero and one never makes two memories differ by more. (ch 31)
- `open_gate_is_a_skip_through_time`: With the gate open the cell is a skip through time. (ch 31)
- `memory_gap_after_many_steps_is_product_of_gates`: After `step_count` steps the difference between two memories has been multiplied by every forget ...

#### [RmsNorm.lean](../lean/SquigglyLine/Supporting/NetworkShape/RmsNorm.lean): RMSNorm and pre-norm.

- `root_mean_square_written_out`: It is the root of the mean of the squares.
- `scaling_a_vector_scales_its_root_mean_square`: Scaling a vector scales its root mean square.
- `rms_norm_forgets_the_scale`: RMSNorm forgets the scale. (ch 24)
- `root_mean_square_after_rms_norm_equals_one`: After RMSNorm the root mean square is one.
- `loss_through_rms_norm_is_scale_invariant`: Any loss read through an RMSNorm is scale invariant. (ch 24)
- `gradient_through_rms_norm_is_at_right_angles_to_weights`: So its gradient is at right angles to the weights. (ch 24)
- `pre_norm_leaves_the_skip_path_alone`: Pre-norm leaves the skip path alone. (ch 24)
- `pre_norm_branch_ignores_the_stream_size`: What a pre-norm branch adds does not depend on the size of the stream. (ch 24)
- `post_norm_resets_the_size`: Post-norm resets the size. (ch 24)

#### [SignedDistance.lean](../lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean): Signed distance functions.

- `nearest_distance_equals_distance_field_at_the_data`: The theorem's distance is the field, read at the data. (ch 29)
- `distance_field_is_at_least_zero`: The field is never negative: a distance is not.
- `line_is_never_empty`: The line is never empty: it has a point above or below any point of space.
- `distance_field_slope_is_at_most_one`: The field is never steep. (ch 27, 29)
- `distance_field_changes_at_most_by_the_distance_moved`: Moving from one point of space to another changes the field by at most the distance between them.
- `graph_of_a_continuous_function_is_closed`: The graph of a continuous function is closed.
- `distance_field_is_zero_exactly_on_the_line`: The field is zero exactly on the line. (ch 29)
- `step_shorter_than_the_field_cannot_reach_the_line`: A step shorter than the field cannot reach the line. (ch 29)
- `safe_step_from_the_height_alone`: A safe step from the height alone. (ch 29)
- `tube_is_where_the_field_is_less_than_radius`: The tube of radius `radius` round the line is where the field is below `radius`. (ch 29)
- `signed_distance_has_the_size_of_nearest_distance`: The signed distance has the size of the nearest-point distance. (ch 29)
- `height_overstates_the_distance`: The height above the line overstates the distance. (ch 29)
- `height_overstates_by_at_most_the_stretch`: And by no more than the slope allows. (ch 29)

#### [SkipAndNorm.lean](../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean): Skip connections and normalisation, as polarizers.

- `plate_keeps_length_of_the_overlap`: Malus's law.
- `crossed_plate_blocks`: Crossed plates block.
- `crossed_plate_with_bypass_does_nothing`: A crossed plate with a bypass does nothing. (ch 31)
- `squared_length_after_a_plate_with_bypass`: The squared length after a plate with a bypass. (ch 31)
- `plate_with_bypass_never_dims`: A plate with a bypass never dims the light. (ch 31)
- `part_along_the_axis_doubles`: The part along the axis doubles.
- `rest_is_left_as_it_was`: The rest is left as it was.
- `part_along_the_axis_after_many_bypass_plates`: After `plate_count` plates with a bypass on the same axis, the part along the axis has grown ... (ch 31)
- `bypass_plates_get_closer_and_never_arrive`: Closer at every plate, never there. (ch 31)
- `amplifier_gives_full_strength`: Full strength.
- `amplifier_of_nothing_is_nothing`: Nothing in, nothing out.
- `plate_and_amplifier_turn_without_loss`: A plate and an amplifier turn the light without loss. (ch 31)
- `plate_and_amplifier_give_full_strength`: With any overlap at all, of either sign, the output has full strength.
- `amplifier_cannot_raise_the_dead`: An amplifier cannot raise the dead. (ch 31)
- `amplified_plates_lose_nothing`: With amplifiers the loss is gone. (ch 30, 31)

#### [Temperature.lean](../lean/SquigglyLine/Supporting/NetworkShape/Temperature.lean): Temperature trades quality for diversity; a codebook snaps to the nearest code.

- `average_score_rises_as_temperature_falls_cross_multiplied`: The cross-multiplied form of "the average score rises with `inverse_temperature`". (ch 39)
- `colder_sampler_picks_better_on_average`: A colder sampler picks better answers on average. (ch 15, 39)
- `snapping_moves_output_at_most_slope_times_distance`: Snapping moves the output by at most slope times distance. (ch 39)
- `nearest_entry_is_the_gentlest_snap`: The nearest entry is the gentlest snap. (ch 39)

#### [UniversalApproximation.lean](../lean/SquigglyLine/Supporting/NetworkShape/UniversalApproximation.lean): Universal approximation, and what it costs.

- `ramp_is_zero_before_its_piece`: Before its piece, a ramp is zero.
- `ramp_rises_inside_its_piece`: Inside its piece, a ramp rises with slope one.
- `ramp_stays_at_full_height_after_its_piece`: After its piece, a ramp stays at its full height.
- `slope_nonneg`: A slope bound is never negative.
- `adding_one_more_ramp`: Adding one more ramp.
- `ramps_follow_the_function_piece_by_piece`: Piece by piece. (ch 32)
- `relu_network_close`: A network of `2 * piece_count` units is within `2 * slope_limit / piece_count` of `model`. (ch 32)
- `universal_approximation`: Universal approximation. (ch 32)

#### [VanishingGradients.lean](../lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean): Vanishing and exploding signals.

- `gain_below_one_dies`: A gain below one dies. (ch 30)
- `gain_above_one_blows_up`: A gain above one blows up. (ch 30)
- `plates_vanish`: A stack of plates with a fixed turn dims the light exponentially. (ch 30)
- `plate_never_lengthens_the_light`: A plate never lengthens the light. (ch 30)
- `plate_acts_the_same_forwards_and_backwards`: A plate acts the same way forwards and backwards. (ch 30)
- `gradient_comes_back_through_the_same_plates`: The gradient comes back through the same plates. (ch 30)
- `bypass_plates_blow_up`: Plates with a bypass blow up. (ch 30)

### Supporting/NewInputs

#### [Averaging.lean](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean): Averages: ensembles, weight averaging, and the ideal denoiser.

- `weighted_squared_distance_to_a_centre_expanded`: Expand the weighted squared distance of the predictions to a center. (ch 37)
- `error_of_the_average_equals_average_error_minus_spread`: The error of the average is the average error minus the spread. (ch 37)
- `ensemble_error_is_at_most_average_member_error`: An ensemble is at least as good as its members are on average. (ch 37)
- `average_slope_is_at_most_steepest_member`: An average is no steeper than its steepest member. (ch 37)
- `averaging_weights_is_averaging_lines`: Averaging weights is averaging lines, for a model linear in its weights. (ch 37)
- `averaged_weights_error_is_at_most_average_member_error`: Averaged weights are at least as good as the members are on average. (ch 37)
- `offsets_from_the_weighted_mean_cancel`: With shares that add to one, the points' offsets from their weighted mean cancel out. (ch 37)
- `weighted_squared_distance_splits_at_the_mean`: The weighted squared distance to any point `target` splits into the weighted squared distance to ... (ch 37)
- `weighted_mean_is_the_best_single_guess`: The weighted mean is the best single guess. (ch 37, 40)
- `ideal_denoiser_equals_weighted_mean_of_examples`: The ideal denoiser is the mean of the examples with softmax shares. (ch 37)
- `ideal_denoiser_is_the_best_guess`: No other guess is better. (ch 37)
- `ideal_denoiser_stays_inside_the_examples`: The ideal denoiser only averages its training set. (ch 37)

#### [BenignOverfitting.lean](../lean/SquigglyLine/Supporting/NewInputs/BenignOverfitting.lean): Benign overfitting: fitting the noise without paying for it.

- `damage_is_at_most_one_over_junk_strength`: The damage is capped by the junk.
- `signal_is_nearly_untouched_by_junk`: The signal is nearly untouched. (ch 44)
- `split_fit_fits_signal_and_noise`: It fits the signal and the noise exactly. (ch 44)
- `split_fit_is_the_nearest_fit`: No fit is nearer. (ch 44)
- `answer_of_split_fit_at_a_new_input`: What the fit does to a new input. (ch 44)
- `noise_damage_at_a_new_input_is_at_most_its_cap`: The damage the noise does to the answer at a new input. (ch 44)
- `benign_overfitting`: Benign overfitting. (ch 44)

#### [BiasVariance.lean](../lean/SquigglyLine/Supporting/NewInputs/BiasVariance.lean): Bias and variance, and what the dial is.

- `floor_shrinks_the_signal_term`: The bias. (ch 43)
- `raising_the_floor_raises_the_bias`: Raising the floor raises the bias. (ch 43)
- `raising_the_floor_lowers_the_variance`: Raising the floor lowers the variance. (ch 43)
- `bias_variance`: Bias squared plus variance. (ch 43)
- `expected_squared_error_splits_into_signal_and_noise`: The split for a signal and a noise. (ch 43)

#### [Counting.lean](../lean/SquigglyLine/Supporting/NewInputs/Counting.lean): Counting: why a count is hard for a model made of averages and slopes.

- `between_two_counts_there_is_a_half`: Between two counts there is a half. (ch 15, 41)
- `equal_scores_give_the_point_half_way`: An attention head that scores two examples equally returns the point half way between them. (ch 15, 41)
- `ideal_denoiser_blends_two_equally_far_examples`: The ideal denoiser blends counts. (ch 15, 41)
- `sharp_count_costs_slope`: Being sharp about a count costs slope. (ch 2, 15, 41)

#### [Dimple.lean](../lean/SquigglyLine/Supporting/NewInputs/Dimple.lean): The dimpled manifold, in the squiggly line picture.

- `dimpled_model_on_the_manifold_equals_profile`: On the manifold, the dimpled function is `profile`.
- `loss_on_the_manifold_does_not_see_the_dimple_slope`: Training cannot see the slope off the manifold. (ch 46)
- `dimple_does_not_move_along_the_manifold`: The adversarial step does not move along the manifold. (ch 46)
- `any_label_is_one_step_off_the_manifold`: Any label is one step off the manifold. (ch 46)
- `length_of_dimple_step_equals_error_over_slope`: The length of the adversarial step is the error divided by the slope. (ch 46)
- `dimpled_model_slope_is_at_most_profile_slope_plus_dimple_slope`: A dimpled function is `(profile_slope_limit + dimple_slope)`-Lipschitz when `profile` is ... (ch 46)
- `nearest_distance_of_dimpled_model_is_between_two_bounds`: The adversarial distance is the error over the slope. (ch 46)

#### [Forgetting.lean](../lean/SquigglyLine/Supporting/NewInputs/Forgetting.lean): Catastrophic forgetting: what a new task costs an old one.

- `forgetting_goes_through_the_cross_kernel`: Forgetting goes through the cross kernel. (ch 45)
- `forgetting_along_one_direction`: Forgetting along one direction. (ch 45)
- `separate_features_forget_nothing`: Separate features, nothing forgotten. (ch 45)
- `forgetting_is_at_most_predict_size_times_distance`: Moving the weights changes the old errors by at most `‖predict‖` times the distance moved. (ch 45)
- `forgetting_is_at_most_predict_size_times_travel`: A ceiling on forgetting. (ch 45)

#### [Mixing.lean](../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean): Mixing: five more things that are averages, and one that is not.

- `message_passing_layer_shrinks_the_spread`: A message-passing layer shrinks the spread. (ch 38)
- `depth_blurs_the_nodes`: Depth blurs the nodes. (ch 38)
- `noising_step_keeps_total_variance_at_one`: The schedule keeps the total variance at one. (ch 38)
- `signal_share_after_many_noising_steps`: The signal's share is the product of the factors `1 - noise_rate`. (ch 38)
- `averaged_model_ignores_the_moves`: The averaged model ignores the moves. (ch 38)
- `averaged_model_is_no_steeper`: And it is no steeper, when the moves keep distances. (ch 38)
- `baseline_pushes_nothing_on_average`: A baseline pushes nothing on average. (ch 38)
- `subtracting_a_baseline_keeps_the_average_push`: So subtracting a baseline from every reward leaves the average push as it was. (ch 38)
- `guidance_moves_along_the_prompt_direction`: Guidance moves from the plain prediction in the direction of the prompt, `1 + guidance_strength` ... (ch 38)
- `guided_step_is_longer_by_one_plus_strength`: The guided step is `1 + guidance_strength` times as long as the plain step. (ch 38)
- `guidance_is_not_an_average`: Guidance is not an average. (ch 38)

#### [Neighbours.lean](../lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean): Nearest neighbours, k-means and contrastive learning: three uses of nearness.

- `nearest_neighbour_error_is_at_most_slope_times_distance`: Nearest neighbours. (ch 40)
- `reassigning_points_does_not_raise_the_cost`: k-means, first half. (ch 40)
- `mean_is_the_best_centre_of_a_cluster`: k-means, second half. (ch 40)
- `softmax_ignores_a_constant_added_to_every_score`: Adding the same number to every score changes no share of the softmax. (ch 40)
- `overlap_of_unit_vectors_equals_one_minus_half_squared_distance`: For two vectors of length one, the dot product is one minus half the squared distance. (ch 40)
- `softmax_of_cosine_equals_softmax_of_distance_for_unit_vectors`: Contrastive learning scores by nearness. (ch 40)
- `softmax_of_overlap_equals_softmax_of_distance`: The same without vectors of length one.

#### [OnAverage.lean](../lean/SquigglyLine/Supporting/NewInputs/OnAverage.lean): Two facts about averages: the median, and random directions.

- `moving_a_centre_away_from_the_median_does_not_help`: Moving a centre up, away from a value that has at most half the points above it, does not lower the ...
- `absolute_error_is_least_at_a_median`: Absolute error is least at a median. (ch 38)
- `random_directions_are_nearly_at_right_angles`: Random directions are nearly at right angles, on average. (ch 38)

#### [Pruning.lean](../lean/SquigglyLine/Supporting/NewInputs/Pruning.lean): Lottery tickets: what pruning costs.

- `strengths_add`: Strengths add. (ch 45)
- `pruning_slows_a_direction_down`: Pruning slows a direction down. (ch 45)
- `winning_ticket`: A winning ticket. (ch 45)
- `HAS_TIGHT_FEATURES.whole_model_has_tight_features`: With orthogonal features on both sides, the whole model has orthogonal features too, and the ...
- `pruning_moves_the_fit_farther`: Pruning moves the fit farther. (ch 45)

#### [SameKernel.lean](../lean/SquigglyLine/Supporting/NewInputs/SameKernel.lean): Same kernel, same predictions.

- `gradient_step_moves_a_prediction_through_the_kernel`: A step moves a prediction through the kernel only. (ch 42)
- `same_kernel_gives_same_predictions`: Same kernel, same predictions. (ch 42)
- `same_kernel_gives_same_final_answer`: Same kernel, same answer in the end. (ch 42)

### Supporting/Training

#### [AdamW.lean](../lean/SquigglyLine/Supporting/Training/AdamW.lean): AdamW: weight decay inside Adam's rescaling, and outside it.

- `decay_inside_adam_is_rescaled_away`: Inside Adam, the strength of the decay is rescaled away. (ch 23)
- `decay_inside_adam_moves_every_weight_alike`: With no gradient from the loss, decay inside Adam moves every weight toward zero by the same ... (ch 23)
- `scaling_the_loss_inside_adam_is_scaling_the_decay`: Inside Adam, making the loss `scale` times larger is the same as making the decay `scale` times ... (ch 23)
- `adamw_shrinks_then_steps`: AdamW shrinks, then steps. (ch 23)
- `adamw_with_no_gradient_shrinks_every_weight`: With no gradient from the loss, AdamW shrinks every weight at the same rate. (ch 23)
- `adamw_with_no_gradient_after_many_steps`: After `step_count` such steps a weight is `(1 - learning_rate * decay) ^ step_count` of what it was. (ch 23)
- `adamw_decay_does_not_depend_on_loss_scale`: AdamW does not care how large the loss is: its decay keeps its strength. (ch 23)

#### [BatchSize.lean](../lean/SquigglyLine/Supporting/Training/BatchSize.lean): Batch size and learning rate.

- `two_small_steps_against_one_big_step`: Two small steps against one big step. (ch 22)
- `two_small_steps_equal_one_big_step_for_separate_batches`: When the batches share nothing, the two are equal. (ch 22)
- `linear_scaling_rule`: The linear scaling rule. (ch 22)

#### [ComputeBudget.lean](../lean/SquigglyLine/Supporting/Training/ComputeBudget.lean): Chinchilla: how to split a compute budget.

- `sum_with_fixed_product_is_at_least_twice_the_root`: A sum with a fixed product. (ch 22)
- `balanced_split_loss_squared`: What the best split buys. (ch 22)
- `balanced_is_optimal`: The best split balances the two terms. (ch 22)
- `balanced_split_has_a_fixed_ratio`: A fixed ratio. (ch 22)
- `balanced_split_scales_together`: They grow together. (ch 22)
- `chinchilla_optimal`: With the floor.
- `balanced_is_optimal_for_any_common_power`: Any common power.

#### [CrossEntropy.lean](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean): Cross-entropy: classification in the same picture.

- `sum_of_exponentials_is_greater_than_zero`: The sum of the exponentials of the scores is positive.
- `softmax_share_is_greater_than_zero`: Every share is positive. (ch 25, 36)
- `softmax_shares_add_to_one`: The shares add up to one. (ch 25, 36)
- `cross_entropy_equals_minus_weighted_log_of_shares`: The usual form of the loss: minus the label-weighted log of the shares.
- `softmax_share_is_less_than_one`: With at least two classes, every share is below one. (ch 25)
- `cross_entropy_of_a_sure_label_is_greater_than_zero`: The loss of a sure label is never zero. (ch 25)
- `cross_entropy_slope_is_prediction_minus_label`: Prediction minus label. (ch 25)
- `log_of_sigmoid`: The log of the sigmoid, written with the exponential of the score.
- `log_of_one_minus_sigmoid`: The log of one minus the sigmoid.
- `log_loss_in_its_usual_form`: The usual form of the loss, with the sigmoid of the score as the prediction.
- `log_loss_slope_is_prediction_minus_label`: Prediction minus label. (ch 25)
- `slope_of_log_loss`: The slope of the loss, as a function of the score.
- `log_loss_is_convex`: The loss is convex in the score.
- `log_loss_of_label_yes_is_greater_than_zero`: For the label "yes" the loss is never zero. (ch 25)
- `no_finite_score_is_best_for_label_yes`: No finite score is best. (ch 25, 27)
- `score_whose_prediction_equals_the_label_is_best`: A score whose prediction equals the label is a best score. (ch 25)
- `soft_label_has_a_finite_best_score`: A soft label has a finite best score. (ch 25)
- `squared_error_step_is_an_error_step`: Squared error is the case "output minus label". (ch 25)
- `error_step_moves_outputs_through_the_kernel`: The same kernel, whatever the loss. (ch 25)
- `same_kernel_gives_same_outputs_for_any_loss`: Same kernel, same learner, whatever the loss. (ch 25)
- `training_stays_in_the_directions_of_the_features`: Training never leaves the directions of the features.
- `training_takes_least_travel_for_any_loss`: Least travel, whatever the loss. (ch 25)
- `total_log_loss_slope_is_error_times_features`: The gradient is error times features. (ch 25)
- `overlap_with_pulled_back_vector_is_a_sum`: That rate is the inner product of `direction` with `A†` applied to the error, so a gradient step on ... (ch 25)
- `total_log_loss_on_a_line_is_at_most_the_blend`: One valley.
- `no_hill_between_two_settings`: No hill between two settings. (ch 25)
- `budget_of_movement_buys_its_share_of_log_loss`: A budget of movement buys at least its share.

#### [Dropout.lean](../lean/SquigglyLine/Supporting/Training/Dropout.lean): Dropout is weight decay.

- `variance_of_the_keep_mask`: The usual dropout mask is `1 / keep_probability` with probability `keep_probability` and `0` ... (ch 21)
- `dropout_adds_a_penalty`: Dropout adds a penalty. (ch 21)
- `dropout_adds_a_penalty_over_a_dataset`: Over a set of examples. (ch 21)
- `dropout_is_weight_decay_for_equal_features`: Dropout is weight decay. (ch 21)

#### [EdgeOfStability.lean](../lean/SquigglyLine/Supporting/Training/EdgeOfStability.lean): The edge of stability.

- `factor_is_less_than_one_exactly_below_two`: The edge is at two. (ch 19)
- `stable_exactly_below_two_over_strength`: Stable exactly below `2 / kernel_strength`. (ch 19)
- `powers_past_the_edge_grow_at_least_linearly`: Past the edge the factor's powers grow at least linearly. (ch 19)
- `size_of_error_along_a_direction_after_many_steps`: After `step_count` steps the size of the error along `direction` is ... (ch 19)
- `shrinks_below_edge`: Below the edge the error never grows. (ch 19)
- `holds_at_edge`: On the edge the error keeps its size. (ch 19)
- `grows_past_edge`: Past the edge the error grows without limit. (ch 19)

#### [GanGame.lean](../lean/SquigglyLine/Supporting/Training/GanGame.lean): The GAN game: the best critic, and why the players spiral.

- `critic_loss_is_a_log_loss_with_a_soft_label`: The critic's loss is a cross-entropy with a soft label. (ch 27)
- `best_critic_predicts_the_real_share`: The best critic predicts the real share. (ch 27)
- `best_critic_exists_where_both_are_present`: Where real and made data are both present, a best critic exists. (ch 27)
- `critic_cannot_tell_when_the_maker_has_won`: When the maker has won, the critic cannot tell. (ch 27)
- `no_score_is_best_where_made_data_is_absent`: Where made data is absent, no score is best. (ch 27)
- `one_game_step_moves_outward`: One step outward. (ch 27)
- `players_spiral_outward`: The players spiral outward. (ch 27)
- `every_game_step_moves_further_from_rest`: Off the resting point, every step moves the players further from it. (ch 27)

#### [KernelSpectrum.lean](../lean/SquigglyLine/Supporting/Training/KernelSpectrum.lean): The whole error, in the kernel's own directions, and the Fourier case.

- `residual_after_many_steps_is_a_sum_over_directions`: The whole error. (ch 18)
- `loss_after_many_steps_is_a_sum_over_directions`: The whole loss. (ch 18)
- `evenly_sampled_wave_sums_to_zero`: Waves sampled at evenly spaced points cancel: if `point_count` steps of `angle_step` make a whole ... (ch 18)
- `sampled_waves_of_different_frequencies_do_not_overlap`: Two sampled waves of different frequencies do not overlap; a wave overlaps a shifted copy of itself ... (ch 18)
- `gap_kernel_stretches_each_sampled_wave`: The kernel of evenly spaced inputs stretches each sampled wave.
- `output_at_one_input_is_overlap_with_weights`: The output at one input is the inner product of its lift with the weights.
- `adjoint_of_predictor_sums_the_lifts`: The adjoint of the predictor sends a vector to the sum of the lifts of the inputs, each weighted by ...
- `kernel_of_predictor_in_coordinates`: The kernel, in coordinates: a sum of the lift kernel against the vector. (ch 18)
- `fourier_direction_is_stretched`: The Fourier version. (ch 18)
- `fourier_spectral_bias`: Spectral bias, the Fourier version. (ch 18)
- `fourier_series_kernel_sees_only_the_gap`: The kernel of a Fourier series sees only the gap. (ch 18)
- `fourier_series_direction_is_stretched`: The Fourier version, with nothing assumed about the kernel. (ch 18)

#### [LeastAction.lean](../lean/SquigglyLine/Supporting/Training/LeastAction.lean): The trained path as a path of least action.

- `moving_along_the_features_is_moving_least`: Moving only along the features is moving least. (ch 17)
- `gradient_descent_stays_in_the_directions_of_the_features`: Gradient descent never wastes movement. (ch 17)
- `gradient_descent_fit_is_the_nearest_fit`: Training takes the least travel. (ch 13, 17, 45)
- `two_turns_keep_at_most_two_equal_turns`: Even steps lose least. (ch 17)
- `even_turns_keep_more`: Evening out two neighbouring plates never loses length. (ch 17)
- `equal_turns_keep_the_most`: Equal turns keep the most, for any number of plates. (ch 17)

#### [Optimisers.lean](../lean/SquigglyLine/Supporting/Training/Optimisers.lean): Optimisers: schedules, the condition number, momentum, and steps on part of

- `schedule_multiplies_its_factors`: A schedule multiplies its factors. (ch 19)
- `schedule_never_grows_the_error_below_the_edge`: While every `learning_rates step * strength` is between zero and two, the error never grows. (ch 19)
- `step_too_large_grows_the_error`: Why warmup. (ch 19)
- `condition_number_sets_the_speed`: The condition number sets the speed. (ch 19)
- `weakest_direction_shrinks_by_exactly_that_factor`: The weakest direction shrinks by exactly that factor, so no direction can be promised more. (ch 19)
- `momentum_step_with_no_momentum_is_the_plain_step`: With no momentum it is the plain step. (ch 19)
- `momentum_moves_the_edge_of_stability`: Momentum moves the edge of stability. (ch 19)
- `flipping_error_at_the_momentum_edge_keeps_its_size`: At that edge the flipping error never dies and never grows. (ch 19)
- `average_of_steps_is_a_step_on_the_average`: An average of steps is a step on the average. (ch 19)
- `step_on_a_random_example_is_the_full_step_on_average`: A step on a random example is the full step on average. (ch 19)

#### [Perceptron.lean](../lean/SquigglyLine/Supporting/Training/Perceptron.lean): The perceptron, XOR, and no free lunch: nearness to a boundary.

- `score_is_at_most_distance_to_a_boundary_point`: A point's score is at most its distance to any one point of the boundary.
- `margin_is_a_distance_to_the_boundary`: The margin is a distance to the boundary. (ch 26)
- `one_more_mistake_adds_that_example`: One more mistake adds that example to the weights.
- `each_mistake_moves_weights_along_the_true_direction`: Each mistake moves the weights at least `margin` along the true direction. (ch 26)
- `each_mistake_adds_at_most_radius_squared`: Each mistake adds at most `radius²` to the squared size of the weights, because the example was on ... (ch 26)
- `perceptron_mistake_bound`: The perceptron makes at most `(radius / margin)²` mistakes. (ch 26)
- `no_flat_boundary_splits_xor`: No flat boundary splits XOR. (ch 26)
- `one_lifted_feature_splits_xor`: One lifted feature is enough. (ch 26)
- `one_fold_splits_xor`: One fold is enough. (ch 26)
- `two_flat_scores_do_not_split_xor`: Two classes with a softmax are still flat.
- `table_lookup_fits_anything`: A table lookup is a lift that fits anything. (ch 26)
- `anchor_score_is_size_minus_squared_distance`: The anchor score is the squared size of the input minus the squared distance from the input to the ...
- `flat_layer_names_the_nearest_anchor`: A flat layer with one score per class names the nearest anchor. (ch 26)
- `anchor_scores_highest_at_itself`: So it tells any set of distinct points apart: at an anchor, its own score is the highest.
- `flip_gives_the_opposite_label`: After the flip, the label at that input is the opposite.
- `flipping_twice_gives_the_labelling_back`: Flipping twice gives back the labelling you started with. (ch 26)
- `no_free_lunch`: No free lunch. (ch 26)
- `flat_is_best_on_an_unseen_label`: With no pattern in the labels, flat is best. (ch 26)

#### [PolicyGradient.lean](../lean/SquigglyLine/Supporting/Training/PolicyGradient.lean): Policy gradient is the cross-entropy push, times the reward.

- `log_of_policy_share_is_minus_cross_entropy`: The log of a policy's share is minus a cross-entropy. (ch 25)
- `push_on_scores_is_action_minus_prediction`: The push on the scores is "action taken minus prediction". (ch 25)
- `policy_gradient`: The policy gradient. (ch 25)

#### [Regularisers.lean](../lean/SquigglyLine/Supporting/Training/Regularisers.lean): Regularisers, each as a charge on slope or a floor on travel.

- `lasso_sets_a_weak_direction_to_zero`: Lasso sets a weak direction to exactly zero. (ch 21)
- `lasso_shortens_a_strong_direction_by_the_penalty`: A direction stronger than the penalty is kept, shortened by exactly the penalty. (ch 21)
- `weight_decay_only_shrinks`: Weight decay only shrinks. (ch 21)
- `input_noise_is_a_charge_on_slope`: Noise on the input is a charge on slope. (ch 21)
- `worst_nudge_costs_at_most_size_times_summed_weights`: The worst nudge costs at most `size_limit` times the summed weights. (ch 21)
- `worst_nudge_costs_exactly_that`: And one nudge costs exactly that. (ch 21)
- `stochastic_depth_on_average`: Stochastic depth. (ch 21)
- `fit_through_two_examples_needs_slope`: Any line through two examples has slope at least their gap in labels over their distance. (ch 21)
- `mixup_asks_for_the_least_slope`: Mixup asks for the least slope. (ch 21)
- `distillation_gives_a_finite_target`: Distillation gives the student a finite target. (ch 21)

#### [Reparam.lean](../lean/SquigglyLine/Supporting/Training/Reparam.lean): Flat minima: flatter is farther.

- `rescaled_model_gives_same_outputs`: Same outputs.
- `rescaled_model_has_same_error`: Same error. (ch 24)
- `rescaled_model_is_flatter_by_scale_squared`: Flatter by `scale²`. (ch 24)
- `fit_distances_scale_with_the_rescaling`: The distances to the fits are all multiplied by `|scale|`.
- `rescaled_model_travels_farther_by_scale`: Farther by `|scale|`. (ch 24)
- `flatter_is_farther`: Flatter is farther. (ch 24)
- `adjoint_of_rescaled_model`: The adjoint of the rescaled model.
- `rescaled_kernel_is_weaker_by_scale_squared`: The kernel is weaker by `scale²`. (ch 24)
- `rescaling_is_a_change_of_step_size`: Rescaling is a change of step size. (ch 24)
- `strength_times_travel_squared_does_not_change`: What does not change. (ch 24)

#### [SmallSteps.lean](../lean/SquigglyLine/Supporting/Training/SmallSteps.lean): Many small steps.

- `square_law_cost_shrinks_with_step_count`: A square-law cost shrinks with the number of steps. (ch 22)
- `proportional_cost_does_not_shrink`: A cost in proportion to the step does not. (ch 22)
- `small_steps_keep`: Many small steps. (ch 22)
- `any_turn_in_enough_plates_keeps_almost_everything`: Any turn, in enough plates. (ch 22)
- `one_plate_keeps_at_most_two_half_plates`: One plate keeps no more than two plates of half the turn.
- `more_plates_never_hurt`: More plates never hurt.

#### [SpectralBias.lean](../lean/SquigglyLine/Supporting/Training/SpectralBias.lean): Spectral bias: strong directions are learned first.

- `larger_rate_leaves_a_smaller_share`: A larger rate leaves a smaller share. (ch 18)
- `learning_cannot_be_hurried`: It cannot be hurried. (ch 18)
- `learning_does_run_out`: It does run out. (ch 18)
- `strong_directions_first`: Strong directions are learned first. (ch 18)
- `one_step_shrinks_one_direction`: One step, one direction. (ch 18)
- `each_direction_runs_on_its_own_clock`: Each direction on its own clock. (ch 18)
- `direction_of_zero_strength_is_never_learned`: Strength zero: never learned. (ch 18)
- `spectral_bias`: Spectral bias. (ch 18)

#### [StepRules.lean](../lean/SquigglyLine/Supporting/Training/StepRules.lean): Rules for the step: Adam, clipping, a subspace, rounding.

- `adam_step_is_the_sign_of_the_gradient`: The step is the sign of the gradient. (ch 23)
- `adam_step_ignores_the_loss_scale`: Multiplying the loss by a positive number changes nothing. (ch 23)
- `adam_moves_every_coordinate_the_same_distance`: Every coordinate with a gradient moves the same distance. (ch 23)
- `sign_step_closes_a_gap_by_the_learning_rate`: A gap closes by `learning_rate` per step, whatever the strength. (ch 23)
- `clipped_gradient_is_at_most_the_limit`: A clipped gradient is no longer than the limit. (ch 23)
- `gradient_within_the_limit_is_left_alone`: A gradient within the limit is left alone. (ch 23)
- `clipping_caps_the_travel`: Clipping caps the travel. (ch 23)
- `confining_the_weights_never_shortens_the_trip`: Confining the weights never shortens the trip. (ch 23)
- `lifted_model_is_additive_in_its_weights`: The model is additive in its weights: the output for summed weights is the sum of the outputs.
- `rounding_moves_each_output_a_little`: Rounding moves each output by at most the rounding error times the size of the features. (ch 23)
- `rounding_changes_the_slope_a_little`: Rounding changes the slope by at most the rounding error times the stretch of the lift. (ch 23)

#### [Symmetry.lean](../lean/SquigglyLine/Supporting/Training/Symmetry.lean): Symmetries: changes to the weights that leave the line alone.

- `gradient_is_at_right_angles_to_the_weights`: The gradient is at right angles to the weights. (ch 24)
- `step_at_right_angles_lengthens_the_weights`: A step at right angles makes the weights longer. (ch 24)
- `gradient_descent_never_shortens_the_weights`: With such a loss, gradient descent never shortens the weights. (ch 24)
- `balance_after_step`: Training keeps the layers in balance. (ch 24)
- `balanced_stays_balanced`: Two layers of equal size are still of equal size after a step. (ch 24)
- `balanced_layers_have_the_same_size`: Balanced layers have the same size, so each carries the same share of the slope ... (ch 24)
- `shuffling_hidden_units_gives_the_same_function`: Shuffling the hidden units gives the same function. (ch 24)

#### [WeightDecay.lean](../lean/SquigglyLine/Supporting/Training/WeightDecay.lean): Weight decay, early stopping and spare parameters are one thing.

- `early_stopping_leaves_at_most_what_weight_decay_leaves`: Early stopping cuts at least as hard as weight decay. (ch 20)
- `matching_penalty_gives_the_same_share`: The matching penalty. (ch 20)
- `weight_decay_leaves_a_share_of_the_residual`: What weight decay leaves. (ch 20)
- `weight_decay_fit_is_a_resting_point`: The resting point. (ch 20)
- `decay_step_rests_at_the_weight_decay_fit`: Gradient descent with weight decay rests there. (ch 20)
- `weight_decay_is_spare_parameters`: Weight decay is spare parameters. (ch 20)
