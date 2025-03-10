# VMCAI '25 Artifact Description
## Correctness Witnesses for Concurrent Programs: Bridging the Semantic Divide with Ghosts

This is the artifact description for our [VMCAI '25 paper "Correctness Witnesses for Concurrent Programs: Bridging the Semantic Divide with Ghosts"](https://doi.org/10.48550/arXiv.2411.16612).
The artifact is available on [Zenodo](https://doi.org/10.5281/zenodo.13863579).

**The description here is provided for convenience and not maintained.**
The artifact contains [Goblint at `vmcai25` git tag](https://github.com/goblint/analyzer/releases/tag/vmcai25).


## Overview

This artifact contains the following components:

    Evaluation Results  ::  The evaluation results, and overview tables (HTML)
                            generated from the raw data.
    Source Code         ::  Source code for Goblint and Ultimate GemCutter,
                            the verification tools used in the experiments
                            for the paper.
    Verifier Binaries   ::  Binaries for Goblint and Ultimate GemCutter.
    Benchmark Programs  ::  Benchmarks used for evaluation of the verifiers.
    Benchmark Witnesses ::  The witnesses generated by Goblint, as used in the
                            experiments.
    BenchExec Tool      ::  The BenchExec benchmarking tool can be used
                            to replicate our results on these benchmarks.

The next section gives instructions on how to setup and quickly get an overview of the artifact.
The subsequent sections then describe each of these components in detail.
The final section gives information on how to reuse this artifact.


## Getting Started

### 1. Setup

The artifact is a virtual machine (VM). Follow these steps to set it up:

* If you have not done so already, install VirtualBox.
  (<https://www.virtualbox.org/wiki/Downloads>)
* Download the artifact.
* Import the artifact via the VirtualBox UI (`File > Import Appliance`)
  or by running `VBoxManage import ghost-witnesses.ova`.

You can then start the VM from the VirtualBox UI.
Login with user `vagrant` and password `vagrant`.
(Note: By default, the user `Ubuntu` may be selected on the login screen. Click on the name and switch to user `vagrant`.)

You may want to install VirtualBox guest additions (<https://www.virtualbox.org/manual/topics/guestadditions.html#guestadditions>).
If the usual installation does not work, try the following steps:

* Add a disk drive to the VM in its settings (the VM must be off for this).
* After starting the VM and logging in, select `Devices > Insert Guest Additions CD image` from the VirtualBox menu.
* Run the following in a terminal:
  `sudo mount /dev/cdrom /mnt && cd /mnt && sudo ./VBoxLinuxAdditions.run`

### 2. Inspect the evaluation results

To extract the table data used in the paper from our raw evaluation results, open a terminal in the VM (`Ctrl+Alt+T`) and run the following commands:

    ~/scripts/analyse-witnesses.py "$HOME/witness-generation/paper-evaluation/goblint.2024-09-02_08-21-23.files"
    cd ~/witness-validation/paper-evaluation/
    WITNESS_DIR="$HOME/witness-generation/paper-evaluation/goblint.2024-09-02_08-21-23.files" ~/scripts/analyse-validation.py

The times for the Table 2 are given first in seconds and then pretty-printed as in the paper.

For a more detailed inspection and visualization of the data, take a look at the generated HTML report.
Just open the file `~/witness-validation/paper-evaluation/results.2024-09-24_22-00-48.table.html` in firefox.
For detailed information, see the ["Evaluation Results" section](#evaluation-results) below.

### 3. Quick Test of the Benchmark Setup

To analyse some programs with Goblint and analyse the generated witnesses with GemCutter, run

    ~/scripts/quick-run.sh

on a console in the VM.
This will analyse a single program with Goblint and generate witnesses using the four analyses described in the paper.
Subsequently, the script will run GemCutter's verification, witness confirmation and witness validation analyses on the example.

The whole run should should conclude successfully for all configurations in about 2min.
This is indicated by the benchmark results `true` printed on the console, and the fact that the final output looks roughly like this:

    Table 1: Witness Confirmation
    =============================
    correct programs
    -----------------------------
    protection-ghost : total= 1 , confirmed= 1 , rejected= 0 , confirmation rate= 100.0 % , resource out= 0
    mutex-meet-ghost : total= 1 , confirmed= 1 , rejected= 0 , confirmation rate= 100.0 % , resource out= 0
    protection-local : total= 1 , confirmed= 1 , rejected= 0 , confirmation rate= 100.0 % , resource out= 0
    mutex-meet-local : total= 1 , confirmed= 1 , rejected= 0 , confirmation rate= 100.0 % , resource out= 0

    confirmation range: 100.0 % -  100.0 %

    incorrect programs
    -----------------------------
    No programs with witnesses found for protection-ghost. Skipping benchmark set...
    No programs with witnesses found for mutex-meet-ghost. Skipping benchmark set...
    No programs with witnesses found for protection-local. Skipping benchmark set...
    No programs with witnesses found for mutex-meet-local. Skipping benchmark set...

    confirmation range: 100.0 % -  0.0 %


    Table 2: Witness Validation
    ===========================
    protection-ghost
    ----------------
    validation   : {'number': 1, 'time': 14, 'time_pretty': 0:00:14}
    verification : {'number': 1, 'time': 12, 'time_pretty': 0:00:12}
                       0 tasks could be validated but not verified

    mutex-meet-ghost
    ----------------
    validation   : {'number': 1, 'time': 13, 'time_pretty': 0:00:13}
    verification : {'number': 1, 'time': 12, 'time_pretty': 0:00:12}
                       0 tasks could be validated but not verified

    protection-local
    ----------------
    validation   : {'number': 1, 'time': 12, 'time_pretty': 0:00:12}
    verification : {'number': 1, 'time': 12, 'time_pretty': 0:00:12}
                       0 tasks could be validated but not verified

    mutex-meet-local
    ----------------
    validation   : {'number': 1, 'time': 13, 'time_pretty': 0:00:13}
    verification : {'number': 1, 'time': 12, 'time_pretty': 0:00:12}
                       0 tasks could be validated but not verified

    ~

    ===============================================================================
    Completed quick benchmark test run.

    Results of witness generation can be found in: /home/vagrant/witness-generation/2024-10-01_08-57-09
    Generated witnesses are located in:            /home/vagrant/witness-generation/2024-10-01_08-57-09/goblint.2024-10-01_08-57-09.files
    Results of witness validation can be found in: /home/vagrant/witness-validation/2024-10-01_08-57-09
    ===============================================================================

For a slightly larger set of experiments, run

    ~/scripts/medium-run.sh

This will run an entire folder of SV-COMP benchmarks through Goblint and subsequently analyse the generated witness with GemCutter.
The whole run should complete in 3-4h.
(Note: This run uses a smaller timeout and memory limit than the full evaluation used in the paper, so the results for individual benchmarks may differ.)

#### Troubleshooting
On certain old host machines, GemCutter fails with `ERROR(7)`, and the log files (`/home/vagrant/witness-validation/YYYY-MM-DD_hh-mm-ss/concurrency-witness-validation-gemcutter.YYYY-MM-DD_hh-mm-ss.logfiles/*.log`) contain a message as follows:

    [2024-10-01 22:04:14,025 INFO  L327       MonitoredProcess]: [MP /home/vagrant/ultimate/releaseScripts/default/UGemCutter-linux/z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in -t:2000 (1)] Waiting until timeout for monitored process
    [2024-10-01 22:04:14,058 FATAL L?                        ?]: An unrecoverable error occured during an interaction with an SMT solver:
    de.uni_freiburg.informatik.ultimate.logic.SMTLIBException: External (MP /home/vagrant/ultimate/releaseScripts/default/UGemCutter-linux/z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in -t:2000 (1) with exit command (exit)) Received EOF on stdin. No stderr output.

This is because the version of Z3 shipped with GemCutter uses certain processor instructions that the host does not support or VirtualBox emulates incorrectly.
In this case, download an official build of Z3 (<https://github.com/Z3Prover/z3/releases/download/z3-4.12.5/z3-4.12.5-x64-glibc-2.31.zip>) and replace the file `~/ultimate/releaseScripts/default/UGemCutter-linux/z3` with the corresponding binary from the official ZIP:

    wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.5/z3-4.12.5-x64-glibc-2.31.zip
    unzip z3-4.12.5-x64-glibc-2.31.zip
    cp z3-4.12.5-x64-glibc-2.31/bin/z3 ~/ultimate/releaseScripts/default/UGemCutter-linux/z3

### 4. Running the Full Experiments

To re-run the full experiments, execute

    ~/scripts/full-run.sh

This script behaves similarly to the smaller variants in the previous sections.
Note however:

- By default the experiments require 16 GB of memory per benchmark (this configuration was used for the experiments in the paper).
    To reproduce this, you will have to modify the VM's settings in VirtualBox and increase the available memory (shutdown the machine while doing so).

    Alternatively, you can run the experiments with a reduced memory limit.
    To do so, modify the environment variable `BENCHMARK_PARAMS`.
    For instance, the following allows only 4GB of memory per benchmark:

        BENCHMARK_PARAMS="-M 4GB" ~/scripts/full-run.sh

- The full evaluation for the paper required around 3 days.
    In this evaluation, we used the benchexec tool to run 14 validation tasks in parallel (occupying up to 28 cores at a time).

    By default, the provided script only runs one benchmark at a time.
    If you have sufficient cores and memory available (adjust the VM settings accordingly), you can run multiple benchmarks in parallel by setting the environment variable `BENCHEXEC_THREADS`. You may also execute the experiments with a reduced timeout.
    For instance, the following command runs 4 benchmarks in parallel at a time (occupying up to 8 cores), and gives each benchmark a 300s timeout and 4GB memory limit:

        BENCHEXEC_THREADS=4 BENCHMARK_PARAMS="-T 300s -M 4GB" ~/scripts/full-run.sh

Naturally, changes to the timeout or memory are expected to affect the evaluation numbers.


## Evaluation Results

The evaluation results that form the basis for the experimental data in the paper can be found in the directory `~/witness-validation/paper-evaluation/`.
The witnesses generated by Goblint that formed the basis for this evaluation can be found in `~/witness-generation/paper-evaluation/`.
See below for detailed info to reproduce the tables and figures of the paper.

The file `~/witness-validation/paper-evaluation/` contains an HTML overview page generated by the BenchExec benchmarking tool, which displays individual results, quantile and scatter plots. Through the filtering sidebar (top right corner), detailed analyses can be made.

The table contains the following configurations :

* `verify` -- GemCutter verification, without any witness
* `verify+validate-goblint-witnesses-{mutex-meet,protection}-{ghost,local}` -- GemCutter witness validation, applied to the 4 different witness sets generated by Goblint.
  In this mode, GemCutter checks if the given witness is valid and the corresponding program is correct.
* `validate-goblint-witnesses-{mutex-meet,protection}-{ghost,local}` -- GemCutter witness _confirmation_, applied to the different witness sets.
  In this mode, described in the paper, GemCutter only checks if the given witness' invariants are correct, but does not prove the corresponding program correct.

The summary table shows how many benchmarks were analysed and the results.

- The row `correct true` indicates tasks that were successfully verified (for `verify`), or where the witness was confirmed resp. validated (for the other configurations).
- The row `correct false` indicates that a bug was found (for `verify`), resp. that witness validation failed and a witness was rejected.
  The latter only happens for programs that are incorrect, hence there can be no valid correctness witness and rejection is expected.
  As witness validation is not possible for incorrect programs, this data is not discussed in the paper and only appears here due to the benchmark setup.
- The row `incorrect false` would indicate that GemCutter finds a supposed bug in a correct program (for `verify`).
  For witness confirmation configurations, it indicates that GemCutter confirmed the correctness witness given by Goblint, for an incorrect program.
  As witness confirmation ignores the program's correctness, these results are expected and do not indicate a problem in one of the tools.

The *Table* tab gives access to detailed evaluation results for each file.
Clicking on a status shows the complete GemCutter log for the benchmark run.

> **Note:** If you are trying to view logs for individual runs through the HTML table (by clicking on the evaluation result `true` or `false`), you may encounter a warning because browsers block access to local files. Follow the instructions in the message to enable log viewing.

As described above (in [section _2. Inspect the evaluation results_](#2-inspect-the-evaluation-results)), the artifact provides python scripts to directly extract the data shown in the paper from the benchmark results.


## Source Code

### GemCutter

Ultimate GemCutter is developed as part of the Ultimate program analysis framework (<https://ultimate-pa.org>) and is implemented in Java. The source code for Ultimate at the time of evaluation can be found in this artifact in the `~/ultimate` directory.

The directory `trunk/source/CACSL2BoogieTranslator/src/de/uni_freiburg/informatik/ultimate/plugins/generator/cacsl2boogietranslator/witness` is of particular interest for the present paper.
The code in this directory handles instrumentation of the program with various witness entries, as part of Ultimate's translation of the original C code to the intermediate verification language Boogie.

More recent versions of Ultimate can be found at <https://github.com/ultimate-pa/ultimate>.

### Goblint

The Goblint analyzer (<https://goblint.in.tum.de>) is developed by TU Munich and University of Tartu. The source code for Goblint at the time of evaluation can be found in this artifact in the `~/goblint` directory.

The code for this paper is the following:

1. `src/witness/witnessGhostVar.ml` and `src/witness/witnessGhost.ml` define the data types for ghost variables.
2. `src/analyses/mutexGhosts.ml` defines the analysis which determines the ghost variables for a specific program and their updates.
3. `src/analyses/basePriv.ml` lines 342-365 define the invariants with mutex ghost variables from non-relational _mutex-meet_ analysis.
4. `src/analyses/apron/relationPriv.apron.ml` lines 717-750 define the invariants with mutex ghost variables from relational _mutex-meet_ analysis.
5. `src/analyses/base.ml` lines 1269-1289 and `src/analyses/apron/relationAnalysis.apron.ml` lines 637-644 define the wrapping of the invariants with multithreaded mode ghost variables.
6. `src/analyses/basePriv.ml` lines 882-909 define the invariants with mutex ghost variables from (non-relational) _protection_ analysis.
7. `src/witness/yamlWitness.ml` lines 398-421 and 589-621 define the YAML output of ghost variables, their updates and the invariants.

More recent versions of Goblint can be found at <https://github.com/goblint>.


## Verifier Binaries

A pre-built binary of GemCutter can be found in `~/ultimate/releaseScripts/default/UGemCutter-linux/`.
For information on how to execute GemCutter, consult the `README` in `~/ultimate/releaseScripts/default/UGemCutter-linux/`.
To build Ultimate GemCutter from scratch, go to `~/ultimate/releaseScripts/default/` and run `./makeFresh.sh`.

A pre-built binary of Goblint is available as `~/goblint/goblint`.
See `~/goblint/README.md` for information on how to run Goblint.
To build Goblint from scratch, run `make setup && make release`.

Both GemCutter and Goblint can be invoked via the BenchExec benchmarking tool (<https://github.com/sosy-lab/benchexec>) which is installed in the VM.
For examples, see the benchmark definition files `~/witness-generation/goblint.xml` resp. `~/witness-validation/gemcutter.xml` and the scripts `~/scripts/generate-witnesses.sh` resp. `~/scripts/validate-witnesses.sh`.


## Benchmark Programs

This artifact includes the benchmark programs on which we evaluated the verifiers.
These benchmarks are taken from the publicly available sv-benchmarks set (<https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks>)
and correspond to the _ConcurrencySafety-Main_ category of SV-COMP'24 (<https://sv-comp.sosy-lab.org/2024/>).
The benchmarks are written in C and use POSIX threads (`pthreads`) to model concurrency.


## Extending & Reusing This Artifact

* **Building a modified version of the VM:** This VM was created using the `vagrant` tool (<https://developer.hashicorp.com/vagrant/>).
    The `Vagrantfile` used to build the artifact, along with several other files used in the build, is included in the directory `~/artifact`.
    This can be used to inspect the setup of the VM, and even build a modified version.

    Note that, to rebuild the VM, some files (e.g. scripts, evaluation results, this README) need to be extracted from the image and placed in a suitable location on your machine.

* **Adding benchmarks:** You can easily add your own benchmarks programs written in C.
    C programs should contain an empty function called `reach_error()`. Goblint and GemCutter then check that this function is never invoked. Certain (gcc) preprocessing steps may be necessary, e.g. to resolve `#include`s. See the SV-COMP benchmarks for examples (the preprocessed files typically have the extension `.i`).

    To run the evaluation on your own programs, you must edit the benchmark definition files `~/witness-generation/goblint.xml.template` resp. `~/witness-validation/gemcutter.xml.template`.
    Replace the `<include>` path specified in the task set `minimal` with your own path.
    You can then simply run `~/scripts/quick-run.sh`.

* **Adding more tools:** As described above, you can reuse the `Vagrantfile` for this artifact and extend it with whatever installation measures are necessary for an additional tool. Also note, that in order to run other tools with BenchExec, you must write a *tool info module* in python (<https://github.com/sosy-lab/benchexec/blob/main/doc/tool-integration.md>).

    Create a new benchmark definition file for your tool (<https://github.com/sosy-lab/benchexec/blob/main/doc/benchexec.md>).
    The existing files `~/witness-generation/goblint.xml.template` resp. `~/witness-validation/gemcutter.xml.template` can serve as an example.

    If you are planning to support generation or validation of correctness witnesses using the proposed format, take a look at the YAML schema definition for the format linked in the paper.
    The schema is also available in this artifact as `~/artifact-files/correctness-witness-schema.yml`.

