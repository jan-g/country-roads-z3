from setuptools import setup, find_packages


setup(
    name="country-roads",
    versioning="dev",
    setup_requires=["setupmeta"],
    packages=find_packages(exclude=["test.*, *.test", "test*"]),
)
