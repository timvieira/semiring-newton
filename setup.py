from setuptools import setup

setup(
    name='newton',
    version='0.1',
    description=(
        "Solve fixpoint systems of equations over commutative semirings."
    ),
    project_url = 'https://github.com/timvieira/prefix-parser',
    install_requires = [
        'leftcorner @ git+https://github.com/rycolab/left-corner',
        'arsenal @ git+https://github.com/timvieira/arsenal',
        'pytest',
    ],
    authors = [
        'Tim Vieira',
    ],
    readme=open('README.md').read(),
    scripts=[],
    packages=['newton'],
)
