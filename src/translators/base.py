class BaseTranslator:
    
    def __init__(self, transform):
        self.transform = transform
        self.translation = ""
        self.translate()
    
    def translate(self):
        raise NotImplementedError("Subclasses must implement translate()")
    
    def __str__(self):
        return self.translation