# whether app

#### 包含了CoreLocation基本用法，AFNetworking基本用法，storyboard的经验，
#### swift中使用obj-c代码的方法，以及json的简单使用方法。

### 总结：
> 1.storyboard中要添加约束，先加对其约束，再加宽高或上下左右距离约束
>
> 2.storyboard中的标签信息的初始值不要乱填，最好置为空
>
> 3.在代码中访问storyboard文档标签对象的方法通常有连线(自动绑定)和tag寻找法
>
> 4.storyboard是一个场景，其中包含多个页面(UIView)的描述，没有代码控制的页面通常没有意义
>   因此xcode规定每一个页面(UIView)都要与一个控制他的代码(控制器)绑定在一起，每一个控制器
>   也只能与一个页面绑定，这里的绑定指控制器自身的view与页面绑定在一起
>
> 5.cocoaPods令管理第三方类库十分方便，具体用法参考笔记或网络
>
> 6.由于许多第三方类库只有obj-c的版本所以要使用swift,obj-c混合编程，具体方法见笔记
>
> 7.ios9以后默认不允许使用http请求了，只能使用https请求，而有很多web服务还不支持https请求
>  可以在info.plist文件中添加NSAppTransportSecurity并在其中添加子项
>   Allow Arbitrary Loads将其值改为yes就可用http请求了
