//
//  GameScene.swift
//  firstTry
//
//  Created by wanglulu on 15/12/3.
//  Copyright (c) 2015年 wanglulu. All rights reserved.
//
/*********************************************************
1.  本Demo包含粒子系统的使用

**********************************************************/


import SpriteKit

class GameScene: SKScene {
   
    var cloud = SKSpriteNode()
    
    override func didMoveToView(view: SKView) {
        //创建一个背景
        let bac = SKSpriteNode(imageNamed: "background.jpg")
        bac.anchorPoint = CGPoint(x: 0, y: 0)
        bac.position = CGPoint(x: 0, y: 0)
        bac.size = self.size
        self.addChild(bac)
        
        cloud = SKSpriteNode(imageNamed: "huaji")
        cloud.size = CGSizeMake(50, 50)
        cloud.position = CGPointMake(self.frame.size.width/2, self.frame.size.height*0.7)
        cloud.zPosition = 3
        
        //
        let came = SKCameraNode()
        self.camera = came
        cloud.addChild(came)

        
        self.addChild(cloud)
        
        //利用sks文件创建一个粒子系统
        let fire = SKEmitterNode(fileNamed: "rainParticle.sks")
        
        //粒子系统的zPosition要用particleZPosition代替，用zPosition不起作用
        fire?.particleZPosition = 2
        
        //让粒子系统始终跟随cloud
        cloud.addChild(fire!)
        
        //通常也要设置targetNode属性，这样就可将粒子直接渲染到targetNode上，
        //targetNode通常是背景(world)节点，这里没有就设为scene了
        //这样可以大大减少开销提高帧数，同时可以使效果逼真，而不是与背景隔离完全跟随cloud(这里是cloud)
        fire?.targetNode = self //self.world(如果有的话)
        
        //fire?.position = CGPointMake(cloud.position.x, cloud.position.y - cloud.size.height/2)
    }
    
    override func touchesBegan(touches: Set<UITouch>, withEvent event: UIEvent?) {
       /* Called when a touch begins */
        for touch: AnyObject in touches{
            let posi = touch.locationInNode(self)
            let act = SKAction.moveTo(posi, duration: 1)
            self.cloud.runAction(act)
        }
        
        print("posi:\(cloud.position)")
    }
    
    
   
    override func update(currentTime: CFTimeInterval) {
        /* Called before each frame is rendered */
    
    }

    
}
