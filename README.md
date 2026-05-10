# SMT4ModPlant

**SMT4ModPlant**  is an open-source framework for semantic-driven feasibility checking and configuration of modular plants. The framework integrates semantic process and resource descriptions, automated transformation into formal SMT constraints, and logic-based validation of resource assignments using the Z3 SMT solver.
This framework parses **General Recipes** in BatchML conform to ISA-88, reads **Asset Administration Shell (AAS)** files with the Capability Description Submodel, and uses the **Z3 SMT solver** to provide feasible modular plant configurations.



## Features

- **Semantic parsing** of general process recipes (BatchML) and resource descriptions (AAS XML, Capability Description Submodel).
- **Automatic mapping** of required and offered capabilities using ontology-based identifiers (Semantic descriptions).
- **SMT-based resource matching and Automated feasibility checking**: Matches recipe requirements against AAS capabilities using **Z3** and proves feasibility by step-to-resouce assignments, property compatibility, and material flow consistency.
- **Generation of SMT-LIB models** encoding all assignment, property, and material flow constraints.
- **Reproducible example data** for all experimental results at _*tests/fixtures/*_ (Example general recipes and resource descriptions HC10, HC20 and HC30).

---


### Prerequisites

* **Python 3.10+**

### Install Dependencies

Run the following commands in your terminal:

```bash
pip install z3-solver lxml
```

---

## License & Acknowledgments

### Project License

The source code of **SMT4ModPlant** is released under the **[MIT License](LICENSE.txt)**.

### Third-Party Components

This project uses third-party libraries distributed under their respective licenses:

* **[Z3 Theorem Prover](https://github.com/Z3Prover/z3)**
  * Used for SMT solving and feasibility checking
  * Licensed under the **MIT License**

* **[Eclipse BaSyx Python SDK](https://pypi.org/project/basyx-python-sdk/)**
  * Used optionally for reading JSON AAS files and converting them to XML-compatible AAS structures
  * Licensed under the **MIT License**

* **[Hatchling](https://hatch.pypa.io/latest/)**
  * Used as the Python build backend defined in `pyproject.toml`
  * Licensed under the **MIT License**

* **[lxml](https://github.com/lxml/lxml)**
  * Listed as a dependency for XML processing and validation workflows
  * Licensed under the **BSD-3-Clause License**
