# LeanAI4Math

This project explores the intersection of formal mathematics and artificial intelligence. It aims to advance automated theorem proving by leveraging annotated theorems and proof scripts in Lean 4, using them to fine-tune Large Language Models (LLMs) for generating automated mathematical proofs.

## Project Goals

- **Annotation of Theorems**: Annotate mathematical theorems directly into Lean 4 proof scripts for better structure and clarity.
- **Data Collection**: Extract and organize theorem-proof pairs for use as training data.
- **LLM Fine-Tuning**: Use the annotated data to improve the performance of LLMs in generating Lean 4 proofs automatically.
- **AI4Math Research**: Provide a foundation for further research at the intersection of AI and formal mathematics.

## Repository Structure

```
LeanAI4Math/
├── Code/
│   ├── 1DownList.py
│   ├── 2GetList.py
│   ├── 3DownEach.py
│   └── list
├── LeanFile/
```

### Code/

- **1DownList.py**: Likely used for downloading or processing lists of theorems or files.
- **2GetList.py**: Probably extracts or generates lists from existing data or directories.
- **3DownEach.py**: Seems to process or download data in batches or for each item in a list.
- **list**: A data file, containing a list of the discriptions of the theorems.

### LeanFile/

- Contains Lean 4 files with annotated theorems and proof scripts.
- Related aspects: Groups, Rings, Fields, Sets, Order theory, Module theory, Lattice theory

## Getting Started

1. **Clone the repository:**
   ```bash
   git clone https://github.com/EricZhongYJ/LeanAI4Math.git
   cd LeanAI4Math
   ```
2. **Requirements:**  
   - Python 3.x (for scripts in the `Code/` directory)
   - Lean 4 (for files in the `LeanFile/` directory)
   - Additional requirements may be specified in the Python scripts themselves.

3. **Usage:**
   - Use the scripts in `Code/` to process or generate data for training models.
   - Explore the `LeanFile/` directory for annotated Lean 4 theorems and proofs.

## Contributing

Contributions are welcome! If you have suggestions for new theorems, proof techniques, or improvements to the AI pipeline, feel free to open an issue or pull request.

## License

This project is provided for academic and research purposes only.

## Acknowledgements

- Inspired by recent advances in automated theorem proving and the Lean mathematical community.
- Thanks to contributors and researchers in AI and formal mathematics.

---

*For questions, feel free to open an issue or contact the maintainer.*
