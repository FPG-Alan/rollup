任意修改代码， 然后在根目录：

```sh
pnpm  run build
```

cd 到当前目录， 然后

```sh
node ../dist/bin/rollup -c ./rollup.config.mjs
```

或者通过 chrome 调试

```sh
node --inspect-brk ../dist/bin/rollup -c ./rollup.config.mjs
```

然后打开 chrome://inspect
