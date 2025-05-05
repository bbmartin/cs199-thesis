# Python to COQ Translator with Automatic Theorem Generation

A program that is able to take Python code from a file and output usable COQ code with theorems that verify the translated code

## Dependencies

* Lark (Version: 1.2.2)

## Executing the program

Make sure first that the libraries listed in `requirements.txt` have been installed.

```
pip install -r requirements.txt
```

The `test.py` file contains the Python code to be converted to COQ. In order to translate said file, run the following:

```
py parse.py
```
