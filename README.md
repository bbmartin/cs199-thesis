# Python to COQ Translator with Automatic Theorem Generation

A program that is able to take Python code from a file and output usable COQ code with theorems that verify the translated code

## Dependencies

* Lark (Version: 1.2.2)

## Executing the program

Make sure first that the libraries listed in `requirements.txt` have been installed.

```
pip install -r requirements.txt
```

The first argument of the command shown below should be the filepath that leads to the Python code to be translated. The second argument is where the output file containing the translated Coq file is located (and will be created if it doesn't exist).

```
python -m src.main input_file.py output_file.txt
```
