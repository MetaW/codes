//
//  ViewController.swift
//  Whether
//
//  Created by wanglulu on 15/12/2.
//  Copyright © 2015年 wanglulu. All rights 
/*************************************************************************
包含了CoreLocation基本用法，AFNetworking基本用法，storyboard的经验，
swift中使用obj-c代码的方法，以及json的简单使用方法。

总结：
1.storyboard中要添加约束，先加对其约束，再加宽高或上下左右距离约束
2.storyboard中的标签信息的初始值不要乱填，最好置为空
3.在代码中访问storyboard文档标签对象的方法通常有连线(自动绑定)和tag寻找法
4.storyboard是一个场景，其中包含多个页面(UIView)的描述，没有代码控制的页面通常没有意义
   因此xcode规定每一个页面(UIView)都要与一个控制他的代码(控制器)绑定在一起，每一个控制器
   也只能与一个页面绑定，这里的绑定指控制器自身的view与页面绑定在一起
5.cocoaPods令管理第三方类库十分方便，具体用法参考笔记或网络
6.由于许多第三方类库只有obj-c的版本所以要使用swift,obj-c混合编程，具体方法见笔记
7.ios9以后默认不允许使用http请求了，只能使用https请求，而有很多web服务还不支持https请求
   可以在info.plist文件中添加NSAppTransportSecurity并在其中添加子项
   Allow Arbitrary Loads将其值改为yes就可用http请求了
*****************************************************************************/

import UIKit

//my import
import CoreLocation
import AFNetworking

//ViewController继承自UIViewController，由于使用了corelocation要实现对应的接口(or协议):CLLocationManagerDelegate
class ViewController: UIViewController, CLLocationManagerDelegate {
    
    //自动绑定storyboard文档中的对象(也可通过tag值在代码中手动绑定)
    @IBOutlet weak var location: UILabel!
    @IBOutlet weak var temperature: UILabel!
    
    
    //使用coreLocation定位
    let locationManager:CLLocationManager = CLLocationManager()
    
    
    
    
    override func viewDidLoad() {
        super.viewDidLoad()
        // Do any additional setup after loading the view, typically from a nib.
        
        //UIView设置背景的方法
        let background = UIImage(named: "pku")
        self.view.backgroundColor = UIColor(patternImage: background!)
        
        //设置delegate用于回调接口中的方法
        locationManager.delegate = self
        
        //设置定位精确度
        locationManager.desiredAccuracy = kCLLocationAccuracyBest
        
        //获取用户地理位置信息权限，此时会弹出选择框，询问用户是否授权
        //可以在选择框中添加附加信息，通过在info.plist中添加NSLocationUsageDescription
        //或NSLocationAlwaysUsageDescription字段，并在其中添加要附加的信息
        //始终允许访问位置信息
        locationManager.requestAlwaysAuthorization()
        //或：使用应用程序期间允许访问位置数据
        //locationManager.requestWhenInUseAuthorization()
        
        //开始定位
        locationManager.startUpdatingLocation()
        
        //debug
        print("start")
    }

    
    
    
    override func didReceiveMemoryWarning() {
        super.didReceiveMemoryWarning()
        // Dispose of any resources that can be recreated.
    }
    
    
//////////////////////////
    
    
    func locationManager(manager: CLLocationManager, didUpdateLocations locations: [CLLocation]){
        //DELEGATE-FUNC:获得位置信息时回调该函数
        
        let location:CLLocation = locations[locations.count-1] as CLLocation
        if(location.horizontalAccuracy > 0)
        {
            //debuge
            print(location.coordinate.latitude)
            print(location.coordinate.longitude)
            print("finished")
            
            
            //调用函数利用位置信息获取天气信息
            updateWhertherInfo(location.coordinate.latitude, longi: location.coordinate.longitude)
            
            //停止定位
            locationManager.stopUpdatingLocation()
        }
    }
    
    
    
    
    func locationManager(manager: CLLocationManager, didFailWithError error: NSError) {
        //DELEGATE-FUNC:定位失败时回调该函数
        print(error)
    }
    
    
    
    
    func updateWhertherInfo(lati:CLLocationDegrees, longi:CLLocationDegrees) -> (){
        //MY-FUNC:通过网络服务利用位置信息获取天气信息
        
        //AFNetworking使用方法(GET)：
        // 1.
        let netManager = AFHTTPRequestOperationManager()
        
        // 2.请求地址及参数，由web服务器决定
        let url = "http://api.openweathermap.org/data/2.5/weather"
        let params = ["lat":lati, "lon":longi, "APPID":"5fb2e24debb441b76d61b17b72e5ee5e"]
        
        // 3.发送GET请求，这里返回的是json包装的数据
        netManager.GET(url, parameters: params,
            success: {(operation:AFHTTPRequestOperation, responseObject:AnyObject) in
                //debug
                print("JSON:" + responseObject.description!)
                
                //解析json
                self.updateUI(responseObject as! NSDictionary)
                
            },
            failure:{(operation:AFHTTPRequestOperation?, error:NSError) in
                print("ERROR:" + error.localizedDescription)
        });
    }
    
    
    
    
    func updateUI(dict:NSDictionary)->(){
        //MY-FUNC:更新UI现实
        
        if let temp = dict["main"]?["temp"] as? Double
        {
            let temperat = (temp - 273.15)*1.8 + 32
            self.temperature.text = "\(temperat)"
            
        }else{
            print("no temperature error")
        }
        
        if let name = dict["name"] as? String
        {
            self.location.text = name
        }else{
            print("no city error")
        }
    }

}

